#!/bin/sh
# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Immutable response-length fixture; the test supplies only the decimal size.
read -r size || exit 2
case "$size" in ''|*[!0-9]*) exit 2 ;; esac
head -c "$size" /dev/zero
