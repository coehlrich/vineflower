package org.jetbrains.java.decompiler.modules.decompiler.exps;

import java.util.List;

public interface PatternExprent {
  List<PatternExprent> getChildExprents();

  default List<VarExprent> getAllVarExprents() {
    return getChildExprents().stream().map(PatternExprent::getAllVarExprents).flatMap(List::stream).toList();
  }
}
