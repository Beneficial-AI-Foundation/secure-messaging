import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.PRFPRNG.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.PRFPRNG.Overview) args