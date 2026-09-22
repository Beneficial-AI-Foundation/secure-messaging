import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'normalize_section_links', Path(__file__).resolve().parents[1] / 'normalize-section-links.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class SectionLinksTest(unittest.TestCase):
    def test_page_links_without_breaking_deep_links(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / 'chapter').mkdir()
            destination = site / 'chapter/index.html'
            destination.write_text('<base href="../"><main><section id="chapter">'
                                   '<h1>Chapter</h1><section id="nested"><h2>Nested</h2>'
                                   '</section></section></main>')
            source = site / 'index.html'
            source.write_text('''<a href="chapter/#chapter">chapter</a>
<a href="chapter/index.html?view=all&amp;x=1#chapter">query</a>
<a href="chapter/#nested">nested</a>
<a href="chapter/#lean-declaration">Lean</a>
<a href="https://elsewhere.example/chapter/#chapter">external</a>
<script>const example = '<a href="chapter/#chapter">chapter</a>';</script>''')
            self.assertEqual(module.normalize(site), 1)
            text = source.read_text()
            self.assertIn('href="chapter/">chapter', text)
            self.assertIn('href="chapter/index.html?view=all&amp;x=1">query', text)
            self.assertIn('href="chapter/#nested"', text)
            self.assertIn('href="chapter/#lean-declaration"', text)
            self.assertIn('href="https://elsewhere.example/chapter/#chapter"', text)
            self.assertIn("const example = '<a href=\"chapter/#chapter\">chapter</a>'", text)
            self.assertEqual(module.normalize(site), 0)

    def test_relative_base_and_fragment_only_links(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / 'chapter').mkdir()
            source = site / 'chapter/index.html'
            source.write_text('''<base href="../"><main><section id="chapter"><h1>Title</h1>
<a href="chapter/#chapter">sidebar</a><a href="#chapter">local</a>
</section></main>''')
            module.normalize(site)
            self.assertIn('href="chapter/">sidebar', source.read_text())
            self.assertIn('href="#chapter">local', source.read_text())

    def test_multi_section_page_keeps_section_anchors(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            source = site / 'index.html'
            source.write_text('''<main><section id="one"><h1>One</h1></section>
<section id="two"><h1>Two</h1></section><a href="index.html#two">Two</a></main>''')
            self.assertEqual(module.normalize(site), 0)


if __name__ == '__main__':
    unittest.main()
