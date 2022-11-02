# PropaFP with GNAT Studio

PropaFP runner executables currently supports GNAT Studio 2022.

## Usage Notes

Currently, PropaFP does not fully support functions.
It is recommended that you translate your functions into procedures when using PropaFP.

## Why3 Driver

You will need to place our [custom driver](propafp.drv) in /path/to/GNATStudio2022/libexec/spark/share/why3/drivers/propafp.drv

## GNATprove Configuration

Now we need to configure GNATprove to recognize our runner executables.

Add the following items to the "provers" list in /path/to/GNATStudio2022/share/spark/config/gnatprove.conf

```json
  ...,
  { "executable" : "/path/to/propafp-run-lppaver",
      "args" : ["-f", "%f", "-p", "/path/to/lppaver"],
      "args_time" : [],
      "args_steps" : [],
      "driver" : "propafp",
      "name" : "propafp-lppaver",
      "shortcut" : "lppaver",
      "version" : "0.1.0.0",
      "in_place" : false,
      "interactive" : false
  },
  { "executable" : "/path/to/propafp-run-lppaver",
      "args" : ["-c", "-f", "%f", "-p", "/path/to/lppaver"],
      "args_time" : [],
      "args_steps" : [],
      "driver" : "propafp",
      "name" : "propafp-lppaver-ce",
      "shortcut" : "lppaver-ce",
      "version" : "0.1.0.0",
      "in_place" : false,
      "interactive" : false
  },
  { "executable" : "/path/to/propafp-run-dreal",
    "args" : ["-f", "%f", "-p", "/path/to/dreal"],
    "args_time" : [],
    "args_steps" : [],
    "driver" : "propafp",
    "name" : "propafp-dreal",
    "shortcut" : "dreal",
    "version" : "0.1.0.0",
    "in_place" : false,
    "interactive" : false
  },
  { "executable" : "/path/to/propafp-run-metitarski",
    "args" : ["-f", "%f", "-p", "/path/to/metitarski", "-c"],
    "args_time" : [],
    "args_steps" : [],
    "driver" : "propafp",
    "name" : "propafp-metitarski",
    "shortcut" : "metitarski",
    "version" : "0.1.0.0",
    "in_place" : false,
    "interactive" : false
  }
  ...
```

## Using with GNATprove

You can call the PropaFP executables in GNAT Studio's 'Manual Proof' mode using the 'name'/'shortcut' from the GNATprove configuration entries.
For example, to call propafp-run-lppaver, we enter 'propafp-lppaver' or 'lppaver'.

Before calling PropaFP in GNAT Studio, we recommend calling the split_goal_wp_conj transformation on the top-level VC.
We recommend giving a high timeout for PropaFP executables.
To set a timeout of 10 minutes, you can enter `propafp-lppaver 600`.

## Real Functions in SPARK Specifications

To use real functions such as sine in SPARK specifications, use our axiomatic specification found [here](../examples/spark/src/reals.ads).
See [examples/spark](../examples/spark) for examples on how to use this module.
