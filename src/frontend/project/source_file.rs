//! Open discovered sources without following a replacement symlink.
//!
//! macOS walks components with descriptor-relative openat and O_NOFOLLOW, which
//! do not require macOS 11's O_NOFOLLOW_ANY. On the Linux architectures below,
//! procfs supplies descriptor-relative paths. Both keep each parent open until
//! its child is acquired without following links. Other targets retain
//! the legacy filesystem trust assumption. This is not a filesystem sandbox or
//! a guarantee against concurrent writes to an already open regular file.
use std::fs::File;
#[cfg(not(target_os = "macos"))]
use std::fs::OpenOptions;
use std::io;
use std::path::Path;

pub(super) fn open(path: &Path) -> io::Result<File> {
    let file = open_platform(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "source must be a regular file",
        ));
    }
    Ok(file)
}

#[cfg(target_os = "macos")]
fn open_platform(path: &Path) -> io::Result<File> {
    use rustix::fs::{Mode, OFlags};
    use std::path::Component;
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    let mut directory = File::from(rustix::fs::open(
        "/",
        OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC,
        Mode::empty(),
    )?);
    let mut components = absolute.components().peekable();
    while let Some(component) = components.next() {
        let name = match component {
            Component::RootDir | Component::CurDir => continue,
            Component::Normal(name) => name,
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "source path must not contain parent traversal",
                ));
            }
        };
        let file = open_macos_child(&directory, name, components.peek().is_some())?;
        if components.peek().is_none() {
            return Ok(file);
        }
        directory = file;
    }
    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        "source path has no file name",
    ))
}

#[cfg(target_os = "macos")]
fn open_macos_child(
    directory: &File,
    name: &std::ffi::OsStr,
    is_directory: bool,
) -> io::Result<File> {
    use rustix::fs::{Mode, OFlags};
    // Every call receives one component and a held parent. NONBLOCK prevents a
    // replacement FIFO from blocking before the regular-file metadata check.
    let flags = OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC;
    let flags = if is_directory {
        flags | OFlags::DIRECTORY
    } else {
        flags
    };
    Ok(File::from(rustix::fs::openat(
        directory,
        name,
        flags,
        Mode::empty(),
    )?))
}

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv64",
        target_arch = "riscv32"
    )
))]
fn open_platform(path: &Path) -> io::Result<File> {
    open_linux(path, Path::new("/proc/self/fd"))
}

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv64",
        target_arch = "riscv32"
    )
))]
fn open_linux(path: &Path, procfs: &Path) -> io::Result<File> {
    use std::os::unix::fs::OpenOptionsExt;
    use std::path::Component;
    // Linux UAPI asm-generic/fcntl.h on these architectures.
    const NOFOLLOW: i32 = 0o400000;
    const DIRECTORY: i32 = 0o200000;
    const NONBLOCK: i32 = 0o4000;
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    let mut directory = OpenOptions::new()
        .read(true)
        .custom_flags(DIRECTORY)
        .open("/")?;
    // Diagnose a missing/inaccessible descriptor filesystem separately from a
    // missing source. Check the actual held descriptor, not just /proc itself.
    procfs_directory(&directory, procfs)?;
    let mut components = absolute.components().peekable();
    while let Some(component) = components.next() {
        let name = match component {
            Component::RootDir | Component::CurDir => continue,
            Component::Normal(name) => name,
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "source path must not contain parent traversal",
                ));
            }
        };
        let child = procfs_directory(&directory, procfs)?.join(name);
        let flags = NOFOLLOW
            | NONBLOCK
            | if components.peek().is_some() {
                DIRECTORY
            } else {
                0
            };
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(flags)
            .open(child)?;
        if components.peek().is_none() {
            return Ok(file);
        }
        // The parent stays open until the child has been acquired atomically.
        directory = file;
    }
    Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        "source path has no file name",
    ))
}

// The injected descriptor root is private and only used by regression tests;
// production never falls back to following the original pathname.
#[cfg(any(
    all(test, unix),
    all(
        target_os = "linux",
        any(
            target_arch = "x86",
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "riscv64",
            target_arch = "riscv32"
        )
    )
))]
fn procfs_directory(directory: &File, procfs: &Path) -> io::Result<std::path::PathBuf> {
    use std::os::fd::AsRawFd;
    let path = procfs.join(directory.as_raw_fd().to_string());
    let unavailable = |cause: String| {
        io::Error::new(
            io::ErrorKind::Unsupported,
            format!(
                "Linux source loading requires accessible procfs descriptors at {}: {cause}",
                procfs.display()
            ),
        )
    };
    let metadata = std::fs::metadata(&path).map_err(|e| unavailable(e.to_string()))?;
    if !metadata.is_dir() {
        return Err(unavailable(
            "held directory descriptor is not accessible as a directory".into(),
        ));
    }
    Ok(path)
}

#[cfg(not(any(
    target_os = "macos",
    all(
        target_os = "linux",
        any(
            target_arch = "x86",
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "riscv64",
            target_arch = "riscv32"
        )
    )
)))]
fn open_platform(path: &Path) -> io::Result<File> {
    OpenOptions::new().read(true).open(path)
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(
            target_os = "linux",
            any(
                target_arch = "x86",
                target_arch = "x86_64",
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "riscv64",
                target_arch = "riscv32"
            )
        )
    )
))]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::symlink;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);

    #[cfg(target_os = "macos")]
    struct MacosDirectory(std::path::PathBuf);

    #[cfg(target_os = "macos")]
    impl MacosDirectory {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "qleisli-macos-openat-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(fs::canonicalize(path).unwrap())
        }
    }

    #[cfg(target_os = "macos")]
    impl Drop for MacosDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn macos_openat_retains_parent_identity_after_path_replacement() {
        use std::io::Read;
        let root = MacosDirectory::new();
        fs::create_dir(root.0.join("nested")).unwrap();
        fs::write(root.0.join("nested/main.qli"), "original").unwrap();
        fs::create_dir(root.0.join("replacement")).unwrap();
        fs::write(root.0.join("replacement/main.qli"), "replacement").unwrap();
        let held =
            open_macos_child(&File::open(&root.0).unwrap(), "nested".as_ref(), true).unwrap();
        fs::rename(root.0.join("nested"), root.0.join("renamed")).unwrap();
        symlink(root.0.join("replacement"), root.0.join("nested")).unwrap();
        let mut original = open_macos_child(&held, "main.qli".as_ref(), false).unwrap();
        let mut text = String::new();
        original.read_to_string(&mut text).unwrap();
        assert_eq!(text, "original");
        assert!(open(&root.0.join("nested/main.qli")).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn macos_fifo_source_replacement_is_rejected_without_a_writer() {
        let root = MacosDirectory::new();
        let source = root.0.join("main.qli");
        fs::write(&source, "original").unwrap();
        let mut discovered = vec![];
        assert!(super::super::collect_qli_files(&root.0, &mut discovered).is_ok());
        assert_eq!(discovered.as_slice(), std::slice::from_ref(&source));
        fs::remove_file(&source).unwrap();
        assert!(
            std::process::Command::new("mkfifo")
                .arg(&source)
                .status()
                .unwrap()
                .success()
        );
        assert_eq!(
            open(&source).unwrap_err().kind(),
            io::ErrorKind::InvalidInput
        );
    }

    #[test]
    fn unavailable_linux_procfs_has_a_targeted_diagnostic() {
        let root = std::env::temp_dir().join(format!(
            "qleisli-procfs-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(root.clone());
        fs::write(root.join("file"), "not a descriptor directory").unwrap();
        for procfs in [root.join("absent"), root.join("file")] {
            let directory = File::open("/").unwrap();
            let error = procfs_directory(&directory, &procfs).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::Unsupported);
            assert!(
                error
                    .to_string()
                    .contains("Linux source loading requires accessible procfs descriptors"),
                "{error}"
            );
            assert!(error.to_string().contains(&procfs.display().to_string()));
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn missing_linux_source_is_not_misreported_as_missing_procfs() {
        let root = std::env::temp_dir().join(format!(
            "qleisli-missing-source-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let error = open(&root.join("main.qli")).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::NotFound);
        assert!(!error.to_string().contains("procfs"));
    }

    #[test]
    fn source_replacement_between_discovery_and_open_cannot_follow_links() {
        let path = std::env::temp_dir().join(format!(
            "qleisli-source-open-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(path.clone());
        let root = fs::canonicalize(path).unwrap();
        fs::create_dir(root.join("nested")).unwrap();
        fs::write(root.join("nested/main.qli"), "original").unwrap();
        fs::write(root.join("outside"), "replacement").unwrap();
        let mut discovered = vec![];
        assert!(super::super::collect_qli_files(&root, &mut discovered).is_ok());
        assert_eq!(discovered, [root.join("nested/main.qli")]);
        let source = &discovered[0];
        let original = open(source).unwrap();
        fs::rename(source, root.join("original")).unwrap();
        symlink(root.join("outside"), source).unwrap();
        assert!(open(source).is_err());
        // An already acquired descriptor still identifies the original file.
        use std::io::Read;
        let mut text = String::new();
        (&original).read_to_string(&mut text).unwrap();
        assert_eq!(text, "original");
        fs::remove_file(source).unwrap();
        fs::write(source, "original").unwrap();
        fs::rename(root.join("nested"), root.join("renamed")).unwrap();
        symlink(root.join("renamed"), root.join("nested")).unwrap();
        assert!(
            open(source).is_err(),
            "an intermediate replacement must also be rejected"
        );
        assert!(
            open(&root.join("renamed")).is_err(),
            "directories are not sources"
        );
        assert!(open(&root.join("original")).is_ok());
    }
}
