"""
PNML parser for 1-safe Petri nets. 
"""

from __future__ import annotations 
import xml.etree.ElementTree as ET
from dataclasses import dataclass, asdict
from typing import Optional, Dict, List, Set, Tuple
import argparse
import json
import sys
import textwrap
import pathlib

# Data classes for Petri net components

@dataclass
class Place:
    id: str
    name: Optional[str] = None
    initial_marking: int = 0
    attributes: Dict[str, str] = None
    
    
@dataclass
class Transition:
    id: str
    name: Optional[str] = None
    attributes: Dict[str, str] = None
    
@dataclass
class Arc:
    id: str
    source: str
    target: str
    inscription: Optional[int] = 1
    
@dataclass
class PetriNet:
    id: str
    places: Dict[str, Place]
    transitions: Dict[str, Transition]
    arcs: List[Arc]
    initial_marking: Dict[str, int]
    

# Handing analysis errors
class PNMLParserError(Exception):
    pass

# Automatic detection of PNML files
class PNMLParser:
    def __init__(self, xml_root: ET.Element):
        self.root = xml_root
        self.ns = self._detect_namespace()
        # storage
        self.places: Dict[str, Place] = {}
        self.transitions: Dict[str, Transition] = {}
        self.arcs: List[Arc] = []
        self.net_id: Optional[str] = None

    def _detect_namespace(self) -> Dict[str, str]:
        """Detect XML namespace from root tag, if any."""
        root_tag = self.root.tag
        if root_tag.startswith("{"):
            uri = root_tag.split("}")[0].lstrip("{")
            return {'pnml': uri}
        return {}

    def _qn(self, tag: str) -> str:
        """Qualified name helper that respects detected namespace (if any)."""
        if not self.ns:
            return tag
        # If tag already has prefix, return as-is; otherwise use namespace
        # We will use format '{uri}tag'
        uri = list(self.ns.values())[0]
        return f'{{{uri}}}{tag}'

    def parse(self) -> PetriNet:
        # Locate <net> element(s). We'll parse the first net found.
        net_tag = self._qn('net')
        net_elem = self.root.find(net_tag)
        if net_elem is None:
            # maybe multiple nets under pnml
            nets = self.root.findall('.//' + net_tag)
            if not nets:
                raise PNMLParserError("No <net> element found in PNML.")
            net_elem = nets[0]
        self.net_id = net_elem.get('id')

        # Many PNMLs put places/transitions inside <page>
        page_tag = self._qn('page')
        pages = net_elem.findall(page_tag)
        if not pages:
            # maybe places/transitions are direct children of net
            container = net_elem
        else:
            # parse all pages (merge their content)
            container = None

        # Choose to iterate pages if present else net
        if pages:
            page_roots = pages
        else:
            page_roots = [net_elem]

        for page in page_roots:
            self._parse_places(page)
            self._parse_transitions(page)
            self._parse_arcs(page)

        # After parsing nodes and arcs, try to infer initial marking if not already set
        initial_marking = {pid: p.initial_marking for pid, p in self.places.items()}

        # Validate arcs reference existing nodes
        self._validate_arcs()

        return PetriNet(
            id=self.net_id,
            places=self.places,
            transitions=self.transitions,
            arcs=self.arcs,
            initial_marking=initial_marking
        )

    def _parse_places(self, parent: ET.Element):
        place_tag = self._qn('place')
        name_tag = self._qn('name')
        initial_tag = self._qn('initialMarking')
        # Iter over place elements
        for p in parent.findall(place_tag):
            pid = p.get('id')
            if pid is None:
                raise PNMLParserError("Place without id encountered.")
            # name (optional)
            name = None
            name_elem = p.find(name_tag)
            if name_elem is not None:
                # name might be nested: <name><text>...</text></name>
                text_elem = name_elem.find(self._qn('text'))
                if text_elem is not None and text_elem.text:
                    name = text_elem.text.strip()
                elif name_elem.text and name_elem.text.strip():
                    name = name_elem.text.strip()
            # initial marking (common variants)
            marking = 0
            # direct child initialMarking -> text
            init_elem = p.find(initial_tag)
            if init_elem is not None:
                # commonly: <initialMarking><text>1</text></initialMarking>
                text_elem = init_elem.find(self._qn('text'))
                if text_elem is not None and text_elem.text and text_elem.text.strip().isdigit():
                    marking = int(text_elem.text.strip())
                else:
                    # sometimes value in init_elem.text
                    if init_elem.text and init_elem.text.strip().isdigit():
                        marking = int(init_elem.text.strip())
            else:
                # some PNML put initial marking in toolspecific or graphics/annotation
                # try to find an attribute 'initialMarking' or 'marking' in any child elements
                for child in p:
                    # check attributes
                    for attrval in child.attrib.values():
                        if attrval.isdigit():
                            marking = int(attrval)
                    # check text
                    if child.text and child.text.strip().isdigit():
                        marking = int(child.text.strip())
            self.places[pid] = Place(id=pid, name=name, initial_marking=marking, attributes=self._collect_attrs(p))

    def _parse_transitions(self, parent: ET.Element):
        trans_tag = self._qn('transition')
        name_tag = self._qn('name')
        for t in parent.findall(trans_tag):
            tid = t.get('id')
            if tid is None:
                raise PNMLParserError("Transition without id encountered.")
            name = None
            name_elem = t.find(name_tag)
            if name_elem is not None:
                text_elem = name_elem.find(self._qn('text'))
                if text_elem is not None and text_elem.text:
                    name = text_elem.text.strip()
                elif name_elem.text and name_elem.text.strip():
                    name = name_elem.text.strip()
            self.transitions[tid] = Transition(id=tid, name=name, attributes=self._collect_attrs(t))

    def _parse_arcs(self, parent: ET.Element):
        arc_tag = self._qn('arc')
        inscription_tag = self._qn('inscription')
        for a in parent.findall(arc_tag):
            aid = a.get('id')
            src = a.get('source')
            tgt = a.get('target')
            if aid is None:
                raise PNMLParserError("Arc without id encountered.")
            if src is None or tgt is None:
                raise PNMLParserError(f"Arc {aid} missing source/target.")
            # inscription (weight) often stored as <inscription><text>n</text></inscription>
            weight = 1
            ins_elem = a.find(inscription_tag)
            if ins_elem is not None:
                text_elem = ins_elem.find(self._qn('text'))
                if text_elem is not None and text_elem.text and text_elem.text.strip().isdigit():
                    weight = int(text_elem.text.strip())
                elif ins_elem.text and ins_elem.text.strip().isdigit():
                    weight = int(ins_elem.text.strip())
            else:
                # try to infer numeric attribute in arc children
                for child in a:
                    if child.text and child.text.strip().isdigit():
                        weight = int(child.text.strip())
            self.arcs.append(Arc(id=aid, source=src, target=tgt, inscription=weight))

    def _collect_attrs(self, elem: ET.Element) -> Dict:
        """Collect any non-structural attributes (like graphics/tool-specific) if needed."""
        attrs = {}
        for k, v in elem.attrib.items():
            attrs[k] = v
        # Could add more parsing for graphics/tool-specific here
        return attrs

    def _validate_arcs(self):
        node_ids = set(self.places.keys()) | set(self.transitions.keys())
        for arc in self.arcs:
            if arc.source not in node_ids:
                raise PNMLParserError(f"Arc {arc.id} references unknown source '{arc.source}'")
            if arc.target not in node_ids:
                raise PNMLParserError(f"Arc {arc.id} references unknown target '{arc.target}'")


def parse_pnml_file(path: str) -> PetriNet:
    tree = ET.parse(path)
    root = tree.getroot()
    parser = PNMLParser(root)
    return parser.parse()


def petri_to_dict(net: PetriNet) -> Dict:
    """Convert PetriNet dataclass to JSON-serializable dict."""
    return {
        'id': net.id,
        'places': {pid: {'name': p.name, 'initial_marking': p.initial_marking, 'attributes': p.attributes}
                   for pid, p in net.places.items()},
        'transitions': {tid: {'name': t.name, 'attributes': t.attributes}
                        for tid, t in net.transitions.items()},
        'arcs': [{'id': a.id, 'source': a.source, 'target': a.target, 'inscription': a.inscription}
                 for a in net.arcs],
        'initial_marking': net.initial_marking
    }


SAMPLE_PNML = """<?xml version="1.0" encoding="UTF-8"?>
<pnml>
  <net id="net1" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="page1">
      <place id="p1">
        <name><text>P1</text></name>
        <initialMarking><text>1</text></initialMarking>
      </place>
      <place id="p2">
        <name><text>P2</text></name>
      </place>
      <transition id="t1"><name><text>T1</text></name></transition>
      <arc id="a1" source="p1" target="t1"/>
      <arc id="a2" source="t1" target="p2"/>
    </page>
  </net>
</pnml>
"""


def run_cli():
    parser = argparse.ArgumentParser(description="PNML Parser (1-safe Petri nets friendly)")
    parser.add_argument('file', nargs='?', help='Path to PNML file (omit to use --test).')
    parser.add_argument('--out', '-o', help='Optional JSON output file for parsed net.')
    parser.add_argument('--test', action='store_true', help='Run on built-in sample PNML (for quick check).')
    args = parser.parse_args()

    if args.test:
        # parse SAMPLE_PNML string
        root = ET.fromstring(SAMPLE_PNML)
        pn = PNMLParser(root).parse()
        print_summary_and_maybe_write(pn, args.out)
        return

    if not args.file:
        parser.print_help()
        return

    path = pathlib.Path(args.file)
    if not path.exists():
        print(f"File {args.file} does not exist.", file=sys.stderr)
        sys.exit(2)

    try:
        pn = parse_pnml_file(str(path))
    except Exception as e:
        print(f"Error parsing PNML: {e}", file=sys.stderr)
        sys.exit(3)

    print_summary_and_maybe_write(pn, args.out)


def print_summary_and_maybe_write(pn: PetriNet, out_path: Optional[str]):
    print("Parsed Petri net summary:")
    print(f"  net id: {pn.id}")
    print(f"  #places: {len(pn.places)}")
    print(f"  #transitions: {len(pn.transitions)}")
    print(f"  #arcs: {len(pn.arcs)}")
    print("  initial marking (place_id: tokens):")
    for pid, tokens in pn.initial_marking.items():
        print(f"    {pid}: {tokens}")
    # Print arcs
    print("  arcs:")
    for a in pn.arcs:
        print(f"    {a.id}: {a.source} -> {a.target} (weight={a.inscription})")
    if out_path:
        d = petri_to_dict(pn)
        with open(out_path, 'w', encoding='utf-8') as f:
            json.dump(d, f, indent=2, ensure_ascii=False)
        print(f"JSON exported to {out_path}")


if __name__ == '__main__':
    run_cli()
