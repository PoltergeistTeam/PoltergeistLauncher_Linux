# PoltergeistLauncher — порт под Linux

Тот же лаунчер, но вместо Win32 + Direct3D11 + WinHTTP используются GLFW + OpenGL3 + libcurl.
Вся логика (версии, Fabric/Forge, аккаунты, моды Modrinth, разбор крашей, интерфейс) осталась прежней.

## Сборка

Debian / Ubuntu:
    sudo apt install build-essential cmake git libglfw3-dev libcurl4-openssl-dev libgl1-mesa-dev zenity
Fedora:
    sudo dnf install gcc-c++ cmake git glfw-devel libcurl-devel mesa-libGL-devel zenity
Arch:
    sudo pacman -S base-devel cmake git glfw curl mesa zenity

    cmake -B build && cmake --build build -j
    ./build/PoltergeistLauncher

(Если GLFW не нашёлся в системе, CMake скачает и соберёт его сам; тогда нужны dev-пакеты X11/Wayland. Остальные библиотеки CMake скачивает сам, как и в Windows-версии.)

## Где что лежит
- Настройки и игра: `~/.local/share/mclauncher` (или `$XDG_DATA_HOME/mclauncher`)
- Скриншоты для фона: `~/.minecraft/screenshots` и папки экземпляров
- Свой шрифт: положи `font.ttf` рядом с бинарником (иначе берётся DejaVu / Liberation / Noto / результат `fc-match`)

## Что изменилось по сравнению с Windows
- Заголовок окна, перетаскивание и кнопки даёт оконный менеджер. Свои кнопки и трей убраны, режим «свернуть при запуске» сворачивает окно в панель задач.
- Java: ищется в /usr/lib/jvm, JAVA_HOME, PATH, ~/.sdkman, ~/.jdks, runtime лаунчера и ~/.minecraft/runtime. Headless-пакеты (без libawt_xawt.so) пропускаются, Minecraft на них не запускается. Если подходящей Java нет, скачивается Temurin JRE (tar.gz).
- Выбор видеокарты: «встроенная/дискретная» теперь задаёт переменные PRIME (DRI_PRIME, __NV_PRIME_RENDER_OFFLOAD).
- Диалоги выбора папки/картинки используют `zenity` или `kdialog`; ссылки и папки открываются через `xdg-open`.
- Нативные библиотеки LWJGL выбираются под x86_64. На ARM64 работают только версии игры, где Mojang выложил linux-arm64 natives.

## OptiFine, остановка и выбор сборки
- OptiFine теперь скачивается с официального **optifine.net** (страница `adloadx` → `downloadx`, как в других лаунчерах). Зеркало BMCLAPI осталось только запасным: если на сайте файла нет или он не отвечает.
- Список сборок OptiFine берётся с optifine.net/downloads (плюс зеркало добавляет недостающее).
- В окне выбора версии для загрузчика OptiFine появился выпадающий список «Сборка» (Авто = лучшая). После клика по версии игры тоже открывается выбор сборки OptiFine, если их несколько. Выбор сохраняется в config.json (`ofbuild`).
- Рядом с кнопкой запуска появилась кнопка **«Остановить»** (идёт загрузка/установка/запуск — прерывает скачивание и убивает установщик/патчер) и **«Закрыть»** (когда игра уже запущена — корректно завершает процесс игры, через 8 секунд добивает SIGKILL). Закрытие кнопкой не показывается как краш.
