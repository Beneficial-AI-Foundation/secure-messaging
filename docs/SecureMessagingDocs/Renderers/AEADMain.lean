import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.AEAD.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.AEAD.Overview) args