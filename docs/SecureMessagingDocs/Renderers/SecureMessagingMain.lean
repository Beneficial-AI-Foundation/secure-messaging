import SecureMessagingDocs.Render
import SecureMessagingDocs.Chapters.SecureMessaging.Overview

def main (args : List String) : IO UInt32 :=
  SecureMessagingDocs.renderManual (%doc SecureMessagingDocs.Chapters.SecureMessaging.Overview) args