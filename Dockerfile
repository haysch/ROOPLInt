FROM haskell:8.8.4-buster as stack-build
WORKDIR /app
ENV EXE_NAME=ROOPLPP

COPY src/ src/
COPY Setup.hs stack.yaml stack.yaml.lock ROOPLPP.cabal README.md LICENSE ./

RUN stack build --verbosity error \
 && cp "$(stack path --local-install-root)/bin/$EXE_NAME" $EXE_NAME

FROM php:8.0.0-apache-buster as web
ENV WWW_PATH=/var/www/html/topps/roopl-playground/

COPY web/ $WWW_PATH
COPY --from=stack-build /app/$EXE_NAME $WWW_PATH
COPY test/ $WWW_PATH/examples
