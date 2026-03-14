---
description: Install ONNX Runtime for the ort crate in a sandboxed environment
triggers:
  - when cargo test or cargo build fails due to ort-sys download error
  - when the user asks to install or set up ONNX Runtime
  - when you see "Failed to GET" errors from ort-sys build script
---

# Install ONNX Runtime (ort) in Sandbox

The `ort` crate's build script (`ort-sys`) tries to download ONNX Runtime static libraries at build time. In sandboxed environments, this often fails with TLS certificate errors because the build script's HTTP client doesn't trust the proxy's certificates, even though `curl` works fine.

## Symptoms

Build failures with messages like:
```
Failed to GET `https://parcel.pyke.io/v2/delivery/ortrs/packages/msort-binary/...`: Connection Failed: tls connection init failed: invalid peer certificate: UnknownIssuer
```

## Fix

### 1. Determine the required ort-sys version

Check Cargo.toml for the pinned ort version:
```bash
grep 'ort' Cargo.toml
```

The ort-sys version and download URL are determined by the ort version. For `ort = "=2.0.0-rc.9"`, the URL is:
```
https://parcel.pyke.io/v2/delivery/ortrs/packages/msort-binary/1.20.0/ortrs_static-v1.20.0-x86_64-unknown-linux-gnu.tgz
```

If you're unsure of the URL, check the build error output — the ort-sys build script prints the full URL it's trying to fetch.

### 2. Download and extract manually

```bash
mkdir -p /tmp/ort-lib
curl -sL https://parcel.pyke.io/v2/delivery/ortrs/packages/msort-binary/1.20.0/ortrs_static-v1.20.0-x86_64-unknown-linux-gnu.tgz -o /tmp/ort-lib/ort.tgz
cd /tmp/ort-lib && tar xzf ort.tgz
```

Verify the library was extracted:
```bash
ls /tmp/ort-lib/onnxruntime/lib/libonnxruntime.a
```

### 3. Set ORT_LIB_LOCATION for builds

Prefix all cargo commands with `ORT_LIB_LOCATION=/tmp/ort-lib/onnxruntime`:

```bash
ORT_LIB_LOCATION=/tmp/ort-lib/onnxruntime cargo test --lib
ORT_LIB_LOCATION=/tmp/ort-lib/onnxruntime cargo build --profile release
ORT_LIB_LOCATION=/tmp/ort-lib/onnxruntime cargo check
```

This tells the ort-sys build script to use the pre-downloaded library instead of fetching it.

### 4. Verify

```bash
ORT_LIB_LOCATION=/tmp/ort-lib/onnxruntime cargo test --lib 2>&1 | tail -5
```

You should see test results instead of a build failure.

## Notes

- The downloaded library persists in `/tmp/ort-lib/` for the session. If the sandbox is reset, you'll need to re-download.
- This only affects the build environment. The ort crate itself works normally once built.
- For different architectures (e.g., aarch64), adjust the URL accordingly — check the ort-sys build script output for the correct URL.
