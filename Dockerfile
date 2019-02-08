FROM rust:1.31

COPY . .

RUN cargo test