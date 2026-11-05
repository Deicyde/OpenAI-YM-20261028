import YM.Next.UV_STRESS.Tiles
import YM.MultipleContact.Multi.Letting

/-! Generic approximations preserving all specified offset patterns at grid-aligned groups. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact.Flight
open Function Filter MeasureTheory Lattice Wilson RG Extraction Table Cells Script Set BigOperators Finset
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {S:Schedule}{I:Type*}[Fintype I][DecidableEq I]
-- may include unused points; only offsets between groups must miss every coordinate tie.
private def avoid (Q:ℕ)(δ:ℝ)(f:I→ E4)(off:I→ Finset E4)(b:Finset I)(g:I→ Cover):Prop:=
    (∀ i∈ b,∀ s:Axis,(g i s).natAbs≤Q) ∧ ∀ i∈b,∀ j∈b,i≠j → ∀ x∈ off i,∀ y∈off j,∀ a:Axis,
        f i a + δ*(g i a:ℝ) +x a ≠ f j a + δ*(g j a:ℝ) + y a
private lemma pick_sep (δ:ℝ)(hδ:0<δ)(z:I→ E4)(off:I→ Finset E4)(f:I→ Cover){b:Finset I}{B:ℕ}(hb:∀i,(off i).card≤B){i:I}:
    let M:ℕ:=4*B*B*Fintype.card I
    ∃ k≤M, ∀j∈b,∀ x∈off i,∀ y∈off j,∀ a:Axis, z i a+δ*k+x a ≠ z j a+δ*(f j a:ℝ)+y a:= by
       intro M
       let hits j (x y : E4) (a:Axis):=(Finset.range (M+1)).filter fun k:ℕ=> z i a+δ*(k:ℝ)+x a = z j a+δ* (f j a:ℝ)+y a
       let m4 j x y:= (univ:Finset Axis).biUnion fun a=> hits j x y a; let m3 j x := (off j).biUnion fun y=>m4 j x y
       let m2 j:= (off i).biUnion fun x=>m3 j x; let m:=b.biUnion m2
       have subunit j x y a : (hits j x y a).card ≤ 1:=card_le_one.mpr (fun u h v h'=> by have he:=mem_filter.mp h|>.2; have he':=mem_filter.mp h'|>.2; exact_mod_cast (show (u:ℝ)=(v:ℝ) from mul_left_cancel₀ hδ.ne' (by linarith only [he,he']) ))
       have small j x y: (m4 j x y).card≤4:=by refine card_biUnion_le.trans ((sum_le_sum (fun a _=> subunit j x y a)).trans (by simp [Axis]))
       have minor j x:(m3 j x).card≤4*B:=by
           apply ((card_biUnion_le (s:=off j)).trans (sum_le_sum fun y _=>small j x y)).trans
           simp only [sum_const,smul_eq_mul]; exact (mul_le_mul_right' (hb j) 4).trans_eq (mul_comm ..)
       have max4 j:(m2 j).card≤4*B*B:= (card_biUnion_le.trans (sum_le_sum (fun x _=>minor j x))).trans (by simp only [sum_const,smul_eq_mul]; exact (mul_le_mul_right' (hb i) _).trans_eq (mul_comm ..))
       have max': m.card≤ M:=card_biUnion_le.trans ((sum_le_sum fun j _=> max4 ..).trans (by simp only [sum_const,smul_eq_mul]; exact (mul_le_mul_right' b.card_le_univ _).trans_eq (mul_comm ..))) -- syntax trans wrong?
       have hrange:(range (M+1)).card=M+1:= Finset.card_range _
       obtain ⟨k,hk,hmiss⟩:=Finset.exists_mem_notMem_of_card_lt_card (max'.trans_lt ((Nat.lt_succ_self _).trans_le (show M+1 ≤ _ by rw [hrange])))
       refine ⟨k,Nat.lt_succ_iff.mp (mem_range.mp hk),fun j hj x hx y hy a h=>hmiss ?_⟩
       exact mem_biUnion.mpr ⟨j,hj,mem_biUnion.mpr ⟨x,hx,mem_biUnion.mpr ⟨y,hy,mem_biUnion.mpr ⟨a,mem_univ _,mem_filter.mpr ⟨hk,(by exact_mod_cast h)⟩⟩⟩⟩⟩
lemma sep_seq (z:I→ E4)(off:I→Finset E4):let A:=4*(∑ i:I,(off i).card)*(∑ i:I,(off i).card)*Fintype.card I; ∀ δ:ℝ,0<δ→∀ b:Finset I, ∃ f:I→ Cover,avoid A δ z off b f:=by
     let b0:= ∑i:I,(off i).card; have hb(i): (off i).card≤b0:= Finset.single_le_sum (f:=fun i:I=>(off i).card) (fun _ _=>Nat.zero_le _) (mem_univ _)
     intro M δ hδ b
     induction b using Finset.induction_on with
     | empty => exact ⟨0,by simp only [avoid, Finset.notMem_empty, false_and,imp_false];simp⟩
     | @insert i b hi ih=>
       obtain ⟨f,hf,hsep⟩:=ih
       obtain ⟨k,hk,hh⟩:= pick_sep δ hδ z off f (b:=b) hb (i:=i); let g:=Function.update f i (fun _=>(k:ℤ))
       have he j(h:j∈b):g j=f j:=Function.update_of_ne (ne_of_mem_of_not_mem h hi) ..
       refine ⟨g, ?_, ?_⟩
       · intro j hj; rcases Finset.mem_insert.mp hj with e|e
         · exact e ▸ (by simpa [g] using hk)
         rw [he _ e]; exact hf _ e
       intro u hu v hv huv
       have hg : g i=(fun _=>(k:ℤ)):=Function.update_self ..
       rcases Finset.mem_insert.mp hu with e|e <;> rcases Finset.mem_insert.mp hv with s|s
       · exact (huv (e ▸ s ▸ rfl)).elim
       · rw [e,hg,he _ s]; simp only [Int.cast_natCast]; exact hh _ s
       · rw [s,hg,he _ e]; intro x hx y hy a ha; exact hh u e y hy x hx a (by simpa using ha.symm)
       rw [he _ s,he _ e]; exact hsep _ e _ s huv
lemma speck (z:I→ E4)(off:I→Finset E4)(S:Schedule):∃ f:ℕ→I→ Cover, let g(m) := S.gridPoint m ∘ (f m);
    (∀i:I,Tendsto (g · i) atTop (𝓝 (z i)) )∧∀ l:ℕ,∀ i j:I,i≠j→∀ u∈off i,∀ v∈off j,∀ a:Axis,g l i a+u a ≠ g l j a+v a:=by
      let B m(i):=(address (S.a m) (points (fun _:Fin 1=>z i))) 0
      let z' m(i):=S.gridPoint m (B m i)
      let cap:=(∑ i∈(univ:Finset I),(off i).card); have he(m):∃ g:I→ Cover,avoid (4*cap*cap*Fintype.card I) (S.a m) (z' m) off univ g:=by
           exact sep_seq (z' m) off (S.a m) (S.a_pos m) univ
      choose g hg using he
      refine ⟨fun m i=>B m i+g m i,fun i=>?_,?_⟩
      swap
      · intro l i j hij u hu v hv a
        have h := (hg l).2 i (Finset.mem_univ _) j (Finset.mem_univ _) hij u hu v hv a
        change (S.a l *((B l i a+ g l i a:ℤ):ℝ)) + u a ≠ (S.a l *((B l j a+ g l j a:ℤ):ℝ)) + v a
        push_cast; rw [mul_add,mul_add]
        exact h
      have hx:=chosen (S:=S) (points (fun _:Fin 1=>z i))
      have ht : Tendsto (z' · i) atTop (𝓝 (z i)):= (show Continuous (fun x:Points 1=>x 0) from by fun_prop).continuousAt.tendsto.comp hx
      have hl(s:Axis): Tendsto (fun m :ℕ=>S.a m*(g m i s:ℝ)) atTop (𝓝 0):=Metric.tendsto_nhds.mpr (fun ε he=> by
           let b0:= (4*cap*cap*Fintype.card I:ℕ)
           have hh : 0*(b0:ℝ)<ε:=by rw [zero_mul]; exact he
           filter_upwards [(S.shrinks.mul_const (b0:ℝ)).eventually (gt_mem_nhds hh)] with m hm
           change |_-0| < ε; rw [sub_zero,abs_mul,abs_of_pos (S.a_pos m),← Int.cast_abs,← Int.natCast_natAbs]
           exact hm.trans_le' (mul_le_mul_of_nonneg_left (by exact_mod_cast ((hg m).1 i (Finset.mem_univ _) s)) (S.a_pos m).le))
      have htotal: Tendsto (fun (m:ℕ) (s:Axis)=>S.a m*(g m i s:ℝ)) atTop (𝓝 (0:Axis → ℝ)):=tendsto_pi_nhds.mpr hl
      convert ht.add ((PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp htotal) using 1
      · ext m k; dsimp only [WithLp.toLp]; change (S.a m*(↑(B m i k+g m i k:ℤ):ℝ)) = S.a m*((B m i k:ℤ):ℝ)+(S.a m * ((g m i k:ℤ):ℝ)); rw [Int.cast_add,mul_add]
      simp
end YM.MultipleContact.Flight
