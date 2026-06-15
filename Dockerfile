# Multi-stage build for rustledger
# Produces a minimal image with static musl binaries

# Build stage
FROM rust:1.96-alpine AS builder

RUN apk add --no-cache musl-dev

WORKDIR /build
COPY . .

RUN cargo build --release --target x86_64-unknown-linux-musl

# Runtime stage - scratch for minimal size
FROM scratch

# Copy the unified rledger binary
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/rledger /usr/local/bin/

# Bean-* compatibility aliases
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-check /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-format /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-query /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-report /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-doctor /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-extract /usr/local/bin/
COPY --from=builder /build/target/x86_64-unknown-linux-musl/release/bean-price /usr/local/bin/

# Default entrypoint - use subcommands like: docker run rledger check file.beancount
ENTRYPOINT ["rledger"]
