#!/bin/sh
# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Immutable test-only failed checker; never emits acceptance.
case "$1" in
    --hierarchy-pending) header='qleisli.native-result 3' ;;
    --hierarchy-request-pending) header='qleisli.native-result 3' ;;
    --hierarchy-fourier-pending) header='qleisli.native-result 3' ;;
    --instrument-pending) header='qleisli.native-result 3' ;;
    --qpe-instrument-pending) header='qleisli.native-result 3' ;;
    *) exit 2 ;;
esac
IFS= read -r variant || exit 2
case "$variant" in
    complete) printf '%s\nerror\ncontract\n' "$header" ;;
    extra) printf '%s\nerror\ncontract\nextra\n' "$header" ;;
    missing-newline) printf '%s\nerror\ncontract' "$header" ;;
    *) exit 2 ;;
esac
exit 1
