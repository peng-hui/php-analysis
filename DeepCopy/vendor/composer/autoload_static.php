<?php

// autoload_static.php @generated by Composer

namespace Composer\Autoload;

class ComposerStaticInita96a9d4fb26c56edb2463abcdf580008
{
    public static $files = array (
        '6124b4c8570aa390c21fafd04a26c69f' => __DIR__ . '/..' . '/myclabs/deep-copy/src/DeepCopy/deep_copy.php',
    );

    public static $prefixLengthsPsr4 = array (
        'D' => 
        array (
            'DeepCopy\\' => 9,
        ),
    );

    public static $prefixDirsPsr4 = array (
        'DeepCopy\\' => 
        array (
            0 => __DIR__ . '/..' . '/myclabs/deep-copy/src/DeepCopy',
        ),
    );

    public static function getInitializer(ClassLoader $loader)
    {
        return \Closure::bind(function () use ($loader) {
            $loader->prefixLengthsPsr4 = ComposerStaticInita96a9d4fb26c56edb2463abcdf580008::$prefixLengthsPsr4;
            $loader->prefixDirsPsr4 = ComposerStaticInita96a9d4fb26c56edb2463abcdf580008::$prefixDirsPsr4;

        }, null, ClassLoader::class);
    }
}
