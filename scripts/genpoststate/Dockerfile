# syntax=docker/dockerfile:1

FROM golang:1.21-alpine AS builder

WORKDIR /app

COPY go.mod go.sum ./
RUN go mod download

COPY . .

RUN CGO_ENABLED=0 GOOS=linux go build -o /genpoststate ./cmd/genpoststate

FROM alpine:latest

RUN addgroup -S appgroup && adduser -S appuser -G appgroup

WORKDIR /

RUN addgroup -S monad && adduser -S -G monad monad

COPY --from=builder --chown=appuser:appgroup /genpoststate /genpoststate

USER appuser

USER monad

ENTRYPOINT ["/genpoststate"]
