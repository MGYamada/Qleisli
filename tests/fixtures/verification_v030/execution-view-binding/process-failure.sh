#!/bin/sh
# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
# Immutable test-only process failures, selected by the invocation link name.
case "${0##*/}" in
    failed-acceptance)
        cat >/dev/null
        printf 'qleisli.qirf-native 2\naccepted\ninspection\n0\n0\n'
        exit 1 ;;
    contract)
        cat >/dev/null
        printf 'qleisli.qirf-native 2\nerror\ncontract\n' ;;
    large-output)
        while :; do printf 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'; done ;;
    sleep) exec sleep 4 ;;
    inherited-pipe) sleep 4 & exit 0 ;;
    empty) exit 0 ;;
    *) exit 2 ;;
esac
