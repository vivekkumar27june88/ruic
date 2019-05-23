import path from 'path';
import babel from 'rollup-plugin-babel';
import resolve from 'rollup-plugin-node-resolve';
import commonjs from 'rollup-plugin-commonjs';
import replace from 'rollup-plugin-replace';
import postcss from 'rollup-plugin-postcss';

export default {
    input: './src/index.js',
    moduleName: 'RUIC',
    sourcemap: true,

    // output: {
    //   file: './build/rrpm.js',
    //   format: 'umd',
    //   name: 'ReactRectanglePopupMenu',
    //   sourcemap: true
    // },

    targets: [
        {
            dest: './build/ruic.js',
            format: 'umd'
        },
        {
            dest: 'build/ruic.module.js',
            format: 'es'
        }
    ],

    plugins: [
        postcss({
            modules: true
        }),
        babel({
            exclude: 'node_modules/**'
        }),
        replace({
            'process.env.NODE_ENV': JSON.stringify('development')
        }),
        resolve(),
        commonjs({
            namedExports: {
                // left-hand side can be an absolute path, a path
                // relative to the current directory, or the name
                // of a module in node_modules
                'node_modules/@material-ui/core/styles/index.js': ['withStyles']
            }
        })
    ],

    external: [
        'react',
        'react-dom',
        '@material-ui/core',
        '@material-ui/icons',
        'material-ui',
        'styled-components',
        'react-fontawesome'
    ],

    globals: {
        react: 'React',
        'react-dom': 'ReactDOM'
    }
};
