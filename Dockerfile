# Cape server image: compile with the JDK, run on a small JRE.
FROM eclipse-temurin:17-jdk-alpine AS build
WORKDIR /src
COPY CapeServer.java .
RUN javac -d /out CapeServer.java

FROM eclipse-temurin:17-jre-alpine
WORKDIR /app
COPY --from=build /out /app
# Hosts set $PORT; 8765 is used when running the image yourself.
ENV PORT=8765 CAPE_DATA=/data/capes.properties
RUN mkdir -p /data
EXPOSE 8765
CMD ["java", "-Xmx128m", "-cp", "/app", "CapeServer"]
