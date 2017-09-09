

### Running BGP

Example with Topology Zoo:

```time python -O  synet/drivers/ebgp_baseline.py topos/topozoo/Cogentco.graphml --comms 1 --peers 1 --prefixes 1```


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