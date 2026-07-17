---
name: Native wheel matrix completion
about: Track WPR0/WPP0 implementation of the native artifact targets
title: "WPP0: implement and validate native wheel matrix"
labels: packaging, native
assignees: ""
---

The WP00 foundation deliberately publishes no native wheel. Complete this checklist
only after WPR0 exposes a full, non-placeholder native capability handshake.

- [ ] manylinux 2.17 x86-64
- [ ] manylinux 2.17 aarch64
- [ ] musllinux 1.2 x86-64
- [ ] musllinux 1.2 aarch64
- [ ] macOS x86-64
- [ ] macOS arm64
- [ ] Windows AMD64
- [ ] Windows ARM64
- [ ] `cp310-abi3` audit and forced-native semantic smoke on native hardware
- [ ] Same-version native/universal resolver test
- [ ] LIC-001 closed and audited before any upload
