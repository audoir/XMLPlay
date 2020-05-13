//~ Copyright (C) 2016-2018: Willem Vree.
//~ This program is free software; you can redistribute it and/or modify it under the terms of the
//~ GNU General Public License as published by the Free Software Foundation; either version 2 of
//~ the License, or (at your option) any later version.
//~ This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
//~ without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
//~ See the GNU General Public License for more details. <http://www.gnu.org/licenses/gpl.html>.

/*globals console:false, require:false */
'use strict'
var instrument, sfFile;
var fs = require ('fs'),
    sf2 = require ('sf2-parser'),
    prc = require ('child_process');
    
function centToHz (ct) {                // abs_cent = 1200 * log2 (f/440) + 6900 == 100 * midi number
    return 440 * Math.pow (2, (ct - 6900) / 1200);
}

function toOgg (xs, smpfrq, enctype) {
    if (useLame) {  // -r = ruwe data, -m m = mono, -q 2 = algoritme kwaliteit, -V 4 = VBR kwaliteit
        var opts = '-r -m m -q 2 -V 4 -s 22050 - -'.split (' ');
        opts [8] = '' + smpfrq; // de sample frequentie
    } else { // -t raw = ruwe data, -b16 = 16 bits, -e si = signed, -c 1 = 1 kanaal, -C -4.2 kwaliteit als boven
        var opts = '-t raw -b 16 -e si -c 1 -r 22050 - -C -4.2 -t ogg -'.split (' ');
        opts [9] = '' + smpfrq; // de sample frequentie
        opts [12] = { mp3: '-4.2', ogg: '4', wav: '1' } [enctype];  // quality, see "man soxformat"
        opts [14] = enctype;    // encoding type wav, mp3, ogg
    }
    var o = prc.spawnSync (useLame ? 'lame' : 'sox', opts, { input: Buffer.from (xs) });
    return o.stdout;
}

function sf2_create (parser, instr, enctype, instvol) {
    var i, sid, gen, parm, sampleRate, sample, scale, tune, ofs, xs,
        infos = parser.getInstruments()[instr].info,
        gatt = -12000, ghold = -12000, gdec = -12000, gsus = 0, gscle, gctun, gftun,
        gatn = 0, gflt = 13508, grel = -12000, gdel = -12000, glfo = 0, g2pt = 0, g2vl = 0,
        eatt = -12000, ehold = -12000, edec = -12000, esus = 0, erel = -12000, e2fl = 0;

    var params = [];        // samples and parameters
    for (i = 0; i < infos.length; i++) {
        gen = infos [i].generator;
        if (gen.sampleID) { // sample bag
            sid = gen.sampleID.amount;
            sampleRate = parser.sampleHeader [sid].sampleRate;
            sample = parser.sample [sid];
            xs = new Int16Array (sample.length + 1152);
            xs.set (sample, 0);
            sample = toOgg (xs.buffer, sampleRate, enctype);    // sample = Int16Array, sample.buffer = ArrayBuffer
        } else {            // global bag
            gatt  = gen.attackVolEnv       ? gen.attackVolEnv.amount    : -12000;
            ghold = gen.holdVolEnv         ? gen.holdVolEnv.amount      : -12000;
            gdec  = gen.decayVolEnv        ? gen.decayVolEnv.amount     : -12000;
            gsus  = gen.sustainVolEnv      ? gen.sustainVolEnv.amount / 10 : 0;     // decibel
            grel  = gen.releaseVolEnv      ? gen.releaseVolEnv.amount   : -12000;
            gatn  = gen.initialAttenuation ? gen.initialAttenuation.amount / 10 : 0;
            gflt  = gen.initialFilterFc    ? gen.initialFilterFc.amount : 13508;    // default 20 kHz = 13507,62 cent
            gdel  = gen.delayModLFO        ? gen.delayModLFO.amount     : -12000;
            glfo  = gen.freqModLFO         ? gen.freqModLFO.amount      : -12000;   // freq = 8.176 * log2 (glfo / 1200) Hz
            g2pt  = gen.modLfoToPitch      ? gen.modLfoToPitch.amount   : 0;        // cent
            g2vl  = gen.modLfoToVolume     ? gen.modLfoToVolume.amount / 10  : 0;   // dB
            eatt  = gen.attackModEnv       ? gen.attackModEnv.amount    : -12000;
            ehold = gen.holdModEnv         ? gen.holdModEnv.amount      : -12000;
            edec  = gen.decayModEnv        ? gen.decayModEnv.amount     : -12000;
            esus  = gen.sustainModEnv      ? gen.sustainModEnv.amount / 10 : 0;
            erel  = gen.releaseModEnv      ? gen.releaseModEnv.amount   : -12000;
            e2fl  = gen.modEnvToFilterFc   ? gen.modEnvToFilterFc.amount : 0;
            gscle = gen.scaleTuning        ? gen.scaleTuning.amount / 100 : 1;
            gctun = gen.coarseTune         ? gen.coarseTune.amount      : 0;
            gftun = gen.fineTune           ? gen.fineTune.amount  / 100 : 0;
            continue;
        }
        parm = {            // instrument bag
            attack:  Math.pow (2, (gen.attackVolEnv  ?  gen.attackVolEnv.amount   : gatt)  / 1200), // timecent = 1200*log2(t)
            hold:    Math.pow (2, (gen.holdVolEnv    ?  gen.holdVolEnv.amount     : ghold) / 1200),
            decay:   Math.pow (2, (gen.decayVolEnv   ?  gen.decayVolEnv.amount    : gdec)  / 1200),
            sustain: gen.sustainVolEnv            ? gen.sustainVolEnv.amount / 10 : gsus,           // decibel
            release: Math.pow (2, (gen.releaseVolEnv ? gen.releaseVolEnv.amount   : grel) / 1200),
            atten:   gen.initialAttenuation  ? gen.initialAttenuation.amount / 10 : gatn,
            filter:  centToHz (gen.initialFilterFc   ? gen.initialFilterFc.amount : gflt),
            lfodel:  Math.pow (2, (gen.delayModLFO   ?  gen.delayModLFO.amount    : gdel)  / 1200), // timecent
            lfofreq: Math.pow (2, (gen.freqModLFO    ?  gen.freqModLFO.amount     : glfo)  / 1200) * 8.176, // zie boven
            lfo2ptc: gen.modLfoToPitch               ? gen.modLfoToPitch.amount   : g2pt,          // cent
            lfo2vol: gen.modLfoToVolume          ? gen.modLfoToVolume.amount / 10 : g2vl,          // decibel
            envatt:  Math.pow (2, (gen.attackModEnv  ?  gen.attackModEnv.amount   : eatt)  / 1200),
            envhld:  Math.pow (2, (gen.holdModEnv    ?  gen.holdModEnv.amount     : ehold) / 1200),
            envdec:  Math.pow (2, (gen.decayModEnv   ?  gen.decayModEnv.amount    : edec)  / 1200),
            envsus:  gen.sustainModEnv            ? gen.sustainModEnv.amount / 10 : esus,
            envrel:  Math.pow (2, (gen.releaseModEnv ? gen.releaseModEnv.amount   : erel) / 1200),
            env2flt: gen.modEnvToFilterFc           ? gen.modEnvToFilterFc.amount : e2fl,
            scale:   gen.scaleTuning                 ? gen.scaleTuning.amount / 100 : gscle,
            ctune:   gen.coarseTune                  ? gen.coarseTune.amount      : gctun,
            ftune:   gen.fineTune                    ? gen.fineTune.amount  / 100 : gftun,
            sampleRate: sampleRate,
            sample:  Buffer.from (sample.buffer).toString ('base64'),
        };
        parm.hold += parm.attack;
        parm.decay = parm.hold + parm.decay * (parm.sustain / 100); // decay = time until -100 dB
        parm.sustain = Math.pow (10, -parm.sustain / 20);           // gain factor at sustain level
        parm.atten = Math.pow (10, (instvol - parm.atten) / 20);    // corrigeer instrument volume  (dB)
        parm.lfo2vol = 1 - Math.pow (10, -parm.lfo2vol / 20);       // dB -> lineaire diepte voor gain (0 < diepte < 1)
        parm.envhld += parm.envatt;
        parm.envdec = parm.envhld + parm.envdec * (parm.envsus / 100);
        parm.envsus = 1 - parm.envsus / 100;    // sustain level 0..1

        if (gen.sampleModes && (gen.sampleModes.amount & 1)) {
            ofs = enctype == 'mp3' ? 1104 : 0;
            parm.loopStart = (parser.sampleHeader[sid].startLoop + ofs) / sampleRate;
            parm.loopEnd   = (parser.sampleHeader[sid].endLoop + ofs)   / sampleRate;
        }

        parm.tune  = parm.ctune;    // semitones relative to pitch at sampleRate
        parm.tune += parm.ftune;
        parm.tune += parser.sampleHeader[sid].pitchCorrection / 100;
        parm.tune -= gen.overridingRootKey ? gen.overridingRootKey.amount : parser.sampleHeader[sid].originalPitch;
        parm.keyRangeLo = gen.keyRange.lo;  // midi numbers
        parm.keyRangeHi = gen.keyRange.hi;

        params [i] = parm;
    }
    return params;
}

function mkInstrument (np, bank, instvol, sf_fnm) { // patch number, bank number, volume correction (dB), path to soundfont
    var data = fs.readFileSync (sf_fnm);
    var parser = new sf2.Parser (data);
    parser.parse();
    var presets = parser.getPresets ();
    var presetMap = {};
    presets.forEach (function (p) {
        if (p.instrument != null) presetMap [[p.header.bank, p.header.preset]] = p.instrument;
    });
    var instrument = presetMap [[bank, np]];
    var parms = sf2_create (parser, instrument, encType, instvol);
    var parmsJs = 'instData = ' + JSON.stringify (parms, null, 1);
    if (bank == 128) np = parseInt (np) + 128
    var ofnm = 'instr' + np + encType + '.js';
    fs.writeFileSync (ofnm, parmsJs);
    console.log (ofnm + ' lengte: ' + parmsJs.length);
}

var encType = 'mp3';    // or 'ogg' or 'wav'
var useLame = 1;
exports.setEncType = function (t) {
    useLame = 0     // using sox now
    encType = t;    // 'mp3', 'ogg' or 'wav'
};
exports.mkInstrument = mkInstrument;