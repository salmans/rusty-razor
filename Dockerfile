FROM rust:1.37

COPY . .

RUN cargo test