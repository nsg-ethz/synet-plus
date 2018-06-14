### Install

1. Install Z3 from master, see https://github.com/Z3Prover/z3

2. Install network graph library dependency first

```
pip install -e git+git@github.com:nsg-ethz/tekton.git#egg=Tekton
# Or from a local clone
pip install -e .
```

3. Install python dependencies

```
pip install -r requirements.txt
```

### An Example use of NetComplete

The example at `synet/examples/bgp_peers.py` shows how to use NetComplete to synthesize Provider/Customer peering policies.

Running
```
python synet/examples/bgp_peers.py outdir
```

### Running NSDI Experiements

Running BGP experiements
```
# BGP
 ./eval_scripts/run-ebgp-experiments.sh
# OSPF
 ./eval_scripts/run-ospf-experiments.sh
```

### Running OSPF
```python synet/drivers/ospf_driver.py --help```

Example

```bash
python synet/drivers/ospf_driver.py  -p [NUMBER OF PATHs generated per iteration] -r [NUMBER OF REQS] -f [TOPO FILE NAME.graphml]
```

```bash
python synet/drivers/ospf_driver.py -r 20 -p 100 -f topos/topozoo/AttMpls.graphml
```


### Running Tests

Commonly used ```nosetests``` options:

- Timing each test case: ```--with-timer```
- Running specific tests with tags ```-a tag=value```
- Running specific test case ```nosetests FILE_PATH:TESTCLASS``` or ```nosetests FILE_PATH:TESTCLASS.TESTCASE```

Running fast tests:
```nosetests --with-timer -a speed=fast test/```

Running slow tests:
```nosetests --with-timer -a speed=slow test/```

Running all tests (fast and slow)
```nosetests --with-timer test```
