#!/bin/sh
# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
# Immutable test-only process failures, selected by the invocation link name.
case "${0##*/}" in
    failed-acceptance)
        cat >/dev/null
        printf 'qleisli.qirf-native 1\naccepted\n0\n0\n'
        exit 1 ;;
    contract)
        cat >/dev/null
        printf 'qleisli.qirf-native 1\nerror\ncontract\n' ;;
    large-output)
        while :; do printf 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'; done ;;
    sleep) exec sleep 4 ;;
    inherited-pipe) sleep 4 & exit 0 ;;
    empty) exit 0 ;;
    *) exit 2 ;;
esac
