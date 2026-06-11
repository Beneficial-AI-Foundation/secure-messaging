import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.FSAEAD.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.FSAEAD.Overview) args