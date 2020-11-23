FROM haskell:8.10-buster

RUN apt-get update && apt-get install alex happy
RUN cabal update

WORKDIR /app

COPY Setup.hs              .
COPY stupid-computer.cabal .
COPY CHANGELOG.md          .
COPY LICENSE               .
COPY src/                  ./src/

RUN ls
RUN cabal install --only-dependencies
RUN cabal build
