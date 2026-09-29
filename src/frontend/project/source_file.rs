//! Open discovered sources without following a replacement symlink.
//!
//! macOS checks all components in one open. On the Linux architectures below,
//! walk from a held directory descriptor; procfs supplies safe descriptor-relative
//! paths without unsafe code or a new production dependency. Other targets retain
//! the legacy filesystem trust assumption. This is not a filesystem sandbox or
//! a guarantee against concurrent writes to an already open regular file.
use std::fs::{File, OpenOptions};
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
    use std::os::unix::fs::OpenOptionsExt;
    // Darwin <sys/fcntl.h>: O_NOFOLLOW_ANY | O_NONBLOCK. The latter prevents
    // blocking on a FIFO substituted for a discovered regular source file.
    OpenOptions::new()
        .read(true)
        .custom_flags(0x20000000 | 0x4)
        .open(path)
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
    use std::os::fd::AsRawFd;
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
        let child =
            std::path::PathBuf::from(format!("/proc/self/fd/{}", directory.as_raw_fd())).join(name);
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
