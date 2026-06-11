import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.SCKA.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.SCKA.Overview) args