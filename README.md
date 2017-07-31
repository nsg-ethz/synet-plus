

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
```nosetests  test --with-timer```