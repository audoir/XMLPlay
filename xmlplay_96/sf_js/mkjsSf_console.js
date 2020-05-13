#!/usr/bin/env node

//~ Copyright (C) 2016-2018: Willem Vree.
//~ This program is free software; you can redistribute it and/or modify it under the terms of the
//~ GNU General Public License as published by the Free Software Foundation; either version 2 of
//~ the License, or (at your option) any later version.
//~ This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
//~ without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
//~ See the GNU General Public License for more details. <http://www.gnu.org/licenses/gpl.html>.

var o = require ('./mkjsSf'),
    fs = require ('fs'),
    prc = require ('child_process');

function hasSox () { try { prc.execSync ('sox --version'); return 1; } catch (e) { return 0; } }
function hasLame () { try { prc.execSync ('lame --help'); return 1; } catch (e) { return 0; } }

var args = process.argv.slice (2);
if (args.length < 4) { console.log ('need 4 args: program, bank, volume, sf2 path'); process.exit (1); }
var program = args [0]
if (!(program >= 0 || program < 128)) { console.log ('0 <= program < 128'); process.exit (1); }
var bank = args [1]
if (!(bank >= 0 || bank < 128)) { console.log ('0 <= bank < 128'); process.exit (1); }
var volume = args [2]   // this is a volume correction in dB
if (!(volume > -100 || volume < 100)) { console.log ('-100 dB <= volume < 100 dB'); process.exit (1); }
var soundfont = args [3]
if (!fs.existsSync (soundfont)) { console.log ('soundfont: "' + soundfont + '" does not exist'); process.exit (1); }
if (args [4]) { // implies SOX
    if (hasSox ()) o.setEncType (args [4]); // -> using sox
    else {
        console.log ('cannot find "sox", trying "lame".');
        args [4] = '';  // -> using Lame
    }
}
if (!args [4] && !hasLame ()) {
    if (hasSox ()) o.setEncType ('mp3');    // -> using sox
    else {
        console.log ('cannot find "lame" or "sox"...');
        console.log ('make sure that either "lame" or "sox" is in your PATH')
        process.exit (1);
    }
}

o.mkInstrument (program, bank, volume, soundfont);
