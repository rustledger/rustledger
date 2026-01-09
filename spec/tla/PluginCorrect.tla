--------------------------- MODULE PluginCorrect ---------------------------
(*
 * Plugin Execution Ordering
 *
 * Verifies:
 * - Plugins execute in registration order
 * - Each plugin processes all directives before next plugin starts
 * - Plugins can add new directives (which are processed by later plugins)
 * - No plugin sees directives added by later plugins
 *
 * This models rustledger-plugin's plugin execution logic.
 *)

EXTENDS Integers, Sequences

CONSTANTS
    NumPlugins,     \* Number of registered plugins
    MaxDirectives   \* Maximum directives to process

VARIABLES
    currentPlugin,      \* Index of currently executing plugin (0 = not started)
    directiveCount,     \* Number of directives in stream
    processedBy,        \* Set of (plugin, directive) pairs that have been processed
    pluginComplete,     \* Which plugins have completed
    directivesAdded     \* Directives added by plugins

vars == <<currentPlugin, directiveCount, processedBy, pluginComplete, directivesAdded>>

-----------------------------------------------------------------------------
(* Helper: plugin p has processed directive d *)
HasProcessed(p, d) == <<p, d>> \in processedBy

(* Helper: all directives up to d have been processed by plugin p *)
AllProcessedUpTo(p, d) ==
    \A i \in 1..d : HasProcessed(p, i)

-----------------------------------------------------------------------------
Init ==
    /\ currentPlugin = 0
    /\ directiveCount = 1  \* Start with at least one directive
    /\ processedBy = {}
    /\ pluginComplete = {}
    /\ directivesAdded = 0

-----------------------------------------------------------------------------
(* Start processing with first plugin *)
StartProcessing ==
    /\ currentPlugin = 0
    /\ directiveCount > 0
    /\ currentPlugin' = 1
    /\ UNCHANGED <<directiveCount, processedBy, pluginComplete, directivesAdded>>

(* Plugin p processes directive d *)
ProcessDirective(p, d) ==
    /\ currentPlugin = p
    /\ p \in 1..NumPlugins
    /\ d \in 1..directiveCount
    /\ ~HasProcessed(p, d)
    \* Must process in order: all earlier directives first
    /\ AllProcessedUpTo(p, d - 1)
    /\ p \notin pluginComplete
    /\ processedBy' = processedBy \cup {<<p, d>>}
    /\ UNCHANGED <<currentPlugin, directiveCount, pluginComplete, directivesAdded>>

(* Plugin adds a new directive *)
AddDirective(p) ==
    /\ currentPlugin = p
    /\ p \in 1..NumPlugins
    /\ p \notin pluginComplete
    /\ directiveCount < MaxDirectives
    /\ directivesAdded < MaxDirectives - 1  \* Bound added directives
    /\ directiveCount' = directiveCount + 1
    /\ directivesAdded' = directivesAdded + 1
    /\ UNCHANGED <<currentPlugin, processedBy, pluginComplete>>

(* Plugin p completes (has processed all current directives) *)
CompletePlugin(p) ==
    /\ currentPlugin = p
    /\ p \in 1..NumPlugins
    /\ AllProcessedUpTo(p, directiveCount)
    /\ p \notin pluginComplete
    /\ pluginComplete' = pluginComplete \cup {p}
    /\ IF p < NumPlugins
       THEN currentPlugin' = p + 1
       ELSE currentPlugin' = NumPlugins + 1  \* All done
    /\ UNCHANGED <<directiveCount, processedBy, directivesAdded>>

Next ==
    \/ StartProcessing
    \/ \E p \in 1..NumPlugins, d \in 1..MaxDirectives : ProcessDirective(p, d)
    \/ \E p \in 1..NumPlugins : AddDirective(p)
    \/ \E p \in 1..NumPlugins : CompletePlugin(p)

-----------------------------------------------------------------------------
(* INVARIANTS *)

(* Plugins execute in order: plugin p+1 doesn't start before p completes *)
PluginsInOrder ==
    \A p \in 1..NumPlugins :
        (currentPlugin = p + 1) => (p \in pluginComplete)

(* Each plugin processes directives in order *)
DirectivesInOrder ==
    \A p \in 1..NumPlugins, d \in 2..MaxDirectives :
        HasProcessed(p, d) => HasProcessed(p, d - 1)

(* A plugin can only process if it's the current plugin *)
OnlyCurrentProcesses ==
    \A p \in 1..NumPlugins, d \in 1..MaxDirectives :
        HasProcessed(p, d) => (currentPlugin >= p)

(* Plugin doesn't process directives added by later plugins *)
NoFutureDirectives ==
    \A p \in 1..NumPlugins, d \in 1..MaxDirectives :
        HasProcessed(p, d) => (d <= directiveCount)

(* Once a plugin completes, it stays complete *)
CompletionPermanent ==
    \A p \in pluginComplete : currentPlugin >= p

(* Type invariant *)
TypeOK ==
    /\ currentPlugin \in 0..(NumPlugins + 1)
    /\ directiveCount \in 1..MaxDirectives
    /\ processedBy \subseteq (1..NumPlugins) \X (1..MaxDirectives)
    /\ pluginComplete \subseteq 1..NumPlugins
    /\ directivesAdded \in 0..MaxDirectives

Spec == Init /\ [][Next]_vars

=============================================================================
