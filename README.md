# README #

This README would normally document whatever steps are necessary to get your application up and running.

### What is this repository for? ###

* This is a package to run (1) transparent logic identification (2) clock-gating verification and synthesis and (3) generate training/testing data to represent circuits for CNN.
* [Learn Markdown](https://bitbucket.org/tutorials/markdowndemo)

### How do I get set up? ###

* This package needs to work with [ABC](https://bitbucket.org/alanmi/abc). Please clone the latest ABC first.
* Configuration

1.  under abc/src/, create a folder called "ext"

2. under abc/src/ext, clone this repository

3. under abc/, execute 
```
#!shell

make -j
```
then you are able to run those external commands now.
#  Commands #
There are four commands officially released. They are related to chapters in Yu-Yun Dai's Ph.D. thesis.

 **Chapter 3 Transparent logic**

*  meowBound: analyze the current GIA and output candidate words (a set of bits) in the Json format. The target GIA should be combinational.
Basic usage: 
```
#!shell

&r <targetFile>; meowBound -J <outputFile>
```


* meowReverse: analyze the current GIA and write out a hierarchical Verilog file, containing transparent blocks and functional blocks.
Usage: 
```
#!shell

&r <targetFile>; meowReverse -V <outputFile>;
```


 ** Chapter 4-7 Verification and Synthesis for Clock-Gating**

*  meowDGSyn: perform (1) dependency graph construction, (2) find candidates for clock-gating and (3) add or remove clock-gating condtions.
Usage for Verification: use the current GIA as the revised circuit (R), read in another golden circuit(G) to find candidates of gated FFs in R, prove them and reduce them. Output circuit is R', where the proved gated FFs are re-synthesized.


```
#!shell

&r <revisedCircuit>; meowDGSyn -G <goldenCircuit> -F <outputCircuit>
```


Usage for Synthesis: explore all candidates in the current GIA and add legal clock-gating conditions to FFs (re-synthesis);


```
#!shell

&r <targetCircuit>; meowDGSyn -F <outputCircuit>
```


**Chapter 8 Circuit Recognition with Deep Learning**

* meowCNN: this command should be run after &if -K 4 (mode 1-4)  or &if -K 3 (mode 5) and output a data file for CNNs.
If -P is used, the target circuit is decomposed into sub-circuits and there are multiple data files generated; 
The target circuit should be combinational.
Usage: 

```
#!shell

&r <inputCircuit>; &if -K 4; meowCNN -F <outputFile> -P <outputFolder/head>
```



### Who do I talk to? ###

* Contact: Yu-Yun Dai, b96901171 at gmail.com for this package.
* Issues for ABC: contact Alan