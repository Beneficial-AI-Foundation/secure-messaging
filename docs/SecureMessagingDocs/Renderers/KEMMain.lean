import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.KEM.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.KEM.Overview) args