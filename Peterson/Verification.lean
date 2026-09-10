import Peterson.Repeated.OvertakingExamples
import Peterson.Repeated.ProgressExamples
import Peterson.Repeated.TraceTests
import Peterson.Safety
import Peterson.Progress
import Peterson.ProgressExamples

/-!
# Peterson theorem verification

This module makes the kernel assumptions of the protected mutual-exclusion
theorem visible to the trusted-check command. It is theorem-path evidence, not
an audit of every declaration in CSLib or Mathlib.
-/

#print axioms Peterson.peterson_mutual_exclusion

#print axioms Peterson.valid_iff
#print axioms Peterson.valid_reachable
#print axioms Peterson.mTr_exists_valid_padding

#print axioms Peterson.step_pc_of_ne_actor
#print axioms Peterson.request_pending
#print axioms Peterson.entry_iff_read
#print axioms Peterson.entry_not_pending
#print axioms Peterson.padding_not_entry
#print axioms Peterson.critical_not_entry
#print axioms Peterson.step_pending_or_entry
#print axioms Peterson.pending_succ_of_not_entry
#print axioms Peterson.pending_of_no_entry

#print axioms Peterson.step_pending_predecessor
#print axioms Peterson.pending_predecessor
#print axioms Peterson.pending_iff_request_history

#print axioms Peterson.protocolFair_of_eventually_not_protocol
#print axioms Peterson.critical_succ_of_not_finish
#print axioms Peterson.criticalCompletes_of_eventually_not_critical
#print axioms Peterson.terminal_padding_admissible
#print axioms Peterson.noRequests_admissible
#print axioms Peterson.noRequests_no_pending_or_entry

#print axioms Peterson.lonePassage_valid
#print axioms Peterson.lonePassage_admissible
#print axioms Peterson.lonePassage_pending_entry
#print axioms Peterson.lonePassage_pending_progress
#print axioms Peterson.lonePassage_terminal

#print axioms Peterson.contention_valid
#print axioms Peterson.contention_admissible
#print axioms Peterson.contention_requests_pending
#print axioms Peterson.contention_entries
#print axioms Peterson.contention_pending_progress
#print axioms Peterson.contention_terminal

#print axioms Peterson.protocolNeglect_valid
#print axioms Peterson.protocolNeglect_not_critical
#print axioms Peterson.protocolNeglect_completion_no_entry
#print axioms Peterson.protocolNeglect_enabled
#print axioms Peterson.protocolNeglect_not_fair
#print axioms Peterson.protocolNeglect_peer_taken
#print axioms Peterson.protocolNeglect_counterexample

#print axioms Peterson.criticalNeglect_valid
#print axioms Peterson.criticalNeglect_tail
#print axioms Peterson.criticalNeglect_fair
#print axioms Peterson.criticalNeglect_old_entry
#print axioms Peterson.criticalNeglect_counterexample

#print axioms Peterson.exitNeglect_valid
#print axioms Peterson.exitNeglect_tail
#print axioms Peterson.exitNeglect_entryFair
#print axioms Peterson.exitNeglect_completes
#print axioms Peterson.exitNeglect_not_fair
#print axioms Peterson.exitNeglect_entry_finish
#print axioms Peterson.exitNeglect_counterexample

#print axioms Peterson.flag_iff_interested_initial
#print axioms Peterson.flag_iff_interested_step
#print axioms Peterson.flag_iff_interested_reachable
#print axioms Peterson.flag_false_iff_reachable
#print axioms Peterson.valid_flag_iff_interested
#print axioms Peterson.valid_flag_false_iff

#print axioms Peterson.step_passageStage
#print axioms Peterson.valid_passageStage_mono
#print axioms Peterson.request_stage
#print axioms Peterson.writeTurn_stage
#print axioms Peterson.writeFlagFalse_stage
#print axioms Peterson.entry_stage
#print axioms Peterson.request_unique
#print axioms Peterson.writeTurn_unique
#print axioms Peterson.writeFlagFalse_unique
#print axioms Peterson.entry_unique

#print axioms Peterson.protocol_enabled
#print axioms Peterson.protocol_pc_succ_of_not_taken
#print axioms Peterson.next_protocol_step

#print axioms Peterson.actor_writes_eventually_absent
#print axioms Peterson.shared_writes_eventually_absent
#print axioms Peterson.step_shared_eq_of_not_write
#print axioms Peterson.valid_shared_succ_of_no_write
#print axioms Peterson.shared_fields_stabilize

#print axioms Peterson.step_write_counter
#print axioms Peterson.no_write_suffix_write_counters
#print axioms Peterson.no_write_suffix_no_critical
#print axioms Peterson.pending_reader_on_no_write_suffix

#print axioms Peterson.first_protocol_step
#print axioms Peterson.flagFirst_step_read
#print axioms Peterson.flagFirst_next_read
#print axioms Peterson.flagFirst_favorable_reader_entry
#print axioms Peterson.flagFirst_progress

#print axioms Peterson.turnFirst_step_read
#print axioms Peterson.turnFirst_next_read
#print axioms Peterson.turnFirst_favorable_reader_entry
#print axioms Peterson.turnFirst_progress
#print axioms Peterson.peterson_global_progress

-- Repeated safety and correspondence.
#print axioms Peterson.Repeated.restart_ranges
#print axioms Peterson.Repeated.invariant_restart
#print axioms Peterson.Repeated.invariant_step
#print axioms Peterson.Repeated.invariant_reachable
#print axioms Peterson.Repeated.repeated_mutual_exclusion
#print axioms Peterson.Repeated.flag_iff_interested_step
#print axioms Peterson.Repeated.flag_iff_interested_reachable
#print axioms Peterson.Repeated.mTr_protocol
#print axioms Peterson.Repeated.mTr_protocol_iff
#print axioms Peterson.Repeated.old_reachable
#print axioms Peterson.Repeated.valid_iff
#print axioms Peterson.Repeated.observation_mTr_erase
#print axioms Peterson.Repeated.valid_prefix_mTr
#print axioms Peterson.Repeated.valid_reachable
#print axioms Peterson.Repeated.valid_mutuallyExclusive
#print axioms Peterson.Repeated.mTr_observation
#print axioms Peterson.Repeated.mTr_exists_valid_padding
#print axioms Peterson.Repeated.TraceTests.solo_cycle
#print axioms Peterson.Repeated.TraceTests.cycles
#print axioms Peterson.Repeated.TraceTests.two_passages
#print axioms Peterson.Repeated.TraceTests.restart_changes_pc
#print axioms Peterson.Repeated.TraceTests.restart_requires_exit

-- Per-request control flow, both interference cases, exact target, and execution witnesses.
#print axioms Peterson.Repeated.protocol_step
#print axioms Peterson.Repeated.restart_pc_eq
#print axioms Peterson.Repeated.request_pending
#print axioms Peterson.Repeated.pending_succ_of_not_entry
#print axioms Peterson.Repeated.pending_of_no_entry
#print axioms Peterson.Repeated.protocol_enabled
#print axioms Peterson.Repeated.protocol_pc_succ_of_not_taken
#print axioms Peterson.Repeated.next_protocol_step
#print axioms Peterson.Repeated.first_protocol_step
#print axioms Peterson.Repeated.flagFirst_next_read
#print axioms Peterson.Repeated.flagFirst_favorable_reader_entry
#print axioms Peterson.Repeated.turnFirst_next_read
#print axioms Peterson.Repeated.turnFirst_favorable_reader_entry
#print axioms Peterson.Repeated.favorable_reader_entry
#print axioms Peterson.Repeated.request_source
#print axioms Peterson.Repeated.pending_not_request
#print axioms Peterson.Repeated.entry_before_next_request
#print axioms Peterson.Repeated.boundary_pc_succ
#print axioms Peterson.Repeated.boundary_before
#print axioms Peterson.Repeated.request_cycle_order
#print axioms Peterson.Repeated.writeTurn_facts
#print axioms Peterson.Repeated.first_turn_write
#print axioms Peterson.Repeated.reader_succ
#print axioms Peterson.Repeated.reader_forever
#print axioms Peterson.Repeated.turn_succ
#print axioms Peterson.Repeated.reader_no_turn_write
#print axioms Peterson.Repeated.favorable_turn_forever
#print axioms Peterson.Repeated.no_turn_write_constant
#print axioms Peterson.Repeated.no_turn_write_no_between
#print axioms Peterson.Repeated.flag_false_succ
#print axioms Peterson.Repeated.exit_eventually_false
#print axioms Peterson.Repeated.critical_eventually_false
#print axioms Peterson.Repeated.peer_eventually_false
#print axioms Peterson.Repeated.pending_eventually_entry
#print axioms Peterson.Repeated.repeated_request_entry
#print axioms Peterson.Repeated.protocolFair_of_eventually_not_protocol
#print axioms Peterson.Repeated.critical_succ_of_not_finish
#print axioms Peterson.Repeated.completes_of_exit
#print axioms Peterson.Repeated.terminal_padding_admissible
#print axioms Peterson.Repeated.cycles_admissible
#print axioms Peterson.Repeated.two_requests_served
#print axioms Peterson.Repeated.embed_valid
#print axioms Peterson.Repeated.embed_taken
#print axioms Peterson.Repeated.embed_entry
#print axioms Peterson.Repeated.embed_fair
#print axioms Peterson.Repeated.embed_completes
#print axioms Peterson.Repeated.protocol_neglect_counterexample
#print axioms Peterson.Repeated.critical_neglect_counterexample
#print axioms Peterson.Repeated.exit_neglect_counterexample

-- Quantitative request boundary, finite event history and sharpness.
#print axioms Peterson.Repeated.readerTurn_step
#print axioms Peterson.Repeated.readerTurn_reachable
#print axioms Peterson.Repeated.entry_guard
#print axioms Peterson.Repeated.pending_flag
#print axioms Peterson.Repeated.no_peer_entry_betweenWrites
#print axioms Peterson.Repeated.betweenWrites_succ
#print axioms Peterson.Repeated.request_betweenWrites
#print axioms Peterson.Repeated.turn_before_peer_entry
#print axioms Peterson.Repeated.reader_interval
#print axioms Peterson.Repeated.favorable_turn_interval
#print axioms Peterson.Repeated.reader_succ_origin
#print axioms Peterson.Repeated.turn_between_entries
#print axioms Peterson.Repeated.no_two_peer_entries
#print axioms Peterson.Repeated.mem_peerEntryIndices
#print axioms Peterson.Repeated.repeated_overtaking_bound
#print axioms Peterson.Repeated.repeated_pre_turn_zero
#print axioms Peterson.Repeated.repeated_after_turn_bound
#print axioms Peterson.Repeated.repeated_bounded_service
#print axioms Peterson.Repeated.OvertakingExamples.witness_valid
#print axioms Peterson.Repeated.OvertakingExamples.witness_tail
#print axioms Peterson.Repeated.OvertakingExamples.witness_admissible
#print axioms Peterson.Repeated.OvertakingExamples.witness_request
#print axioms Peterson.Repeated.OvertakingExamples.witness_turn
#print axioms Peterson.Repeated.OvertakingExamples.witness_service
#print axioms Peterson.Repeated.OvertakingExamples.witness_peer_entry
#print axioms Peterson.Repeated.repeated_overtaking_sharp
