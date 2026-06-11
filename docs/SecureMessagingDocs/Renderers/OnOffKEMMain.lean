import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.OnOffKEM.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.OnOffKEM.Overview) args