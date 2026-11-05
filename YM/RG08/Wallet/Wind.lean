import YM.RG08.Wallet.Mortar

/-! # Periodic windings vanish **only** in bulk limit of formal batches

Use around a step for Ward, not real wind/IR. Filter index Nat all grids.
Tail norm supplied on all n for convenience. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {α I : Type} {M : Row α α} {n r e s a : ℕ} {w A : ℝ} {δ : ℕ→ℝ} {m : ℕ→ Side}

/-- Each strict event FINITE and needs only strip qualitative on this comparison.
Not a long-transfer bound. -/
def Glows (F : Shale α r) := ∃ w A, 0<w ∧ Glow F w A
def Vanished (F : ℕ→Shale α r) := ∃ (w : ℝ) (δ : ℕ→ℝ), 0<w ∧ Tendsto δ atTop (𝓝 0) ∧ ∀ i,Glow (F i) w (δ i)
def Mending (F : ℕ→ Shale α r) (K : Shale α r) := Glows K ∧ Vanished (fun i=> F i-K)

variable {F H : Shale α r} {U V : ℕ → Shale α r}

lemma Glows.zero : Glows (0:Shale α r) := ⟨1,0,one_pos,Charge.zero _⟩
lemma Glows.scale (h : Glows F) (s : ℝ) : Glows (s • F) := by obtain ⟨w,C,hp,H⟩ := h; exact ⟨_,_,hp,H.scale s⟩
lemma Glows.plus (h : Glows F) (u : Glows H) : Glows (F+H) := by
  obtain ⟨w,C,hp,H⟩:=h; obtain ⟨v,D,hq,U⟩:=u; exact ⟨_,_,lt_min hp hq,(glow_less H (min_le_left w v) le_rfl).add (glow_less U (min_le_right w v) le_rfl) (fun i=> (ling_pos _ _).le)⟩
lemma Glows.summable (h : Glows F) : Summable F := by obtain ⟨w,D,hp,H⟩:=h; exact H.summable (ling_one hp.le)
lemma Vanished.zero : Vanished (0:ℕ → Shale α r) := ⟨1,fun _=>0,one_pos,tendsto_const_nhds,fun _=>Charge.zero _⟩
lemma Vanished.scale (h : Vanished U) (s : ℝ) : Vanished (s • U) := by
  obtain ⟨w,δ,hp,hδ,hv⟩:=h; exact ⟨w,fun i=>‖s‖*δ i,hp,by simpa using hδ.const_mul ‖s‖,fun i=>(hv i).scale s⟩
lemma Vanished.plus (h : Vanished U) (p : Vanished V) : Vanished (U+V) := by
  obtain ⟨w,δ,hp,hδ,H⟩:=h; obtain ⟨v,R,hq,hR,H'⟩:=p
  refine ⟨min w v,fun i => δ i + R i, lt_min hp hq,by simpa using hδ.add hR,fun i=>?_⟩
  exact (glow_less (H i) (min_le_left ..) le_rfl).add (glow_less (H' i) (min_le_right ..) le_rfl) (fun i=> (ling_pos _ _).le)
lemma Vanished.ever (h : Vanished U) (i : ℕ) : Glows (U i) := by obtain ⟨w,δ,hp,hδ,H⟩:=h; exact ⟨_,_,hp,H i⟩
lemma Mending.scale (h : Mending U F) (s : ℝ) : Mending (s • U) (s • F) :=
  ⟨h.1.scale s,by simp only [Pi.smul_apply,← smul_sub]; exact h.2.scale s⟩
lemma Mending.plus (h : Mending U F) (p : Mending V H) : Mending (U+V) (F+H) := by
  constructor
  · exact h.1.plus p.1
  rw [show _=(fun i=> U i-F) + (fun i=> V i-H) from (funext fun i=> by dsimp; abel : (fun i=> (U+V) i-(F+H))=_)]
  exact h.2.plus p.2
lemma Mending.sums {U : I→ℕ→Shale α r} {F : I→Shale α r} (s : Finset I) (hp : ∀ i∈s,Mending (U i) (F i)) :
    Mending (fun j=> ∑ i∈s,U i j) (∑ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact ⟨Glows.zero,by simp only [sub_self]; exact Vanished.zero⟩ -- forward ref fix
  | insert i s hi ih => simp_rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).plus (ih (fun i hi=> hp i (mem_insert_of_mem hi)))
lemma Mending.one (s : Shale α r) (h : Glows s) : Mending (fun _=>s) s := ⟨h,by simp only [sub_self]; exact Vanished.zero⟩
lemma Mending.ever (h : Mending U F) (i : ℕ) : Glows (U i) := by simpa only [sub_add_cancel] using (show Glows (U i-F+F) from (h.2.ever i).plus h.1)

lemma dropped {F : Shale α (r+2)} (h : Glows F) (he : Whole M) (hp : Tendsto (fun i=>(m i).val) atTop atTop) :
    Vanished (fun i=> rumba M (.some (m i)) F-rumba M none F) := by
  obtain ⟨w,A,hw,H⟩:=h; obtain ⟨v,Q,hv,J⟩:=he
  have hs : Summable F := H.summable (ling_one hw.le)
  let f (n : ℕ) : Shale α (r+2) := F*tuneS M (.some (m n))-F*tuneS M none
  have he i : rumba M (.some (m i)) F-rumba M none F= pool (f i) stems :=
    (pool_minus _ (spinS _ hs ⟨_,_,hv,J⟩) (spinS _ hs ⟨_,_,hv,J⟩)).symm
  let g n (i : Beads α (r+2)) := ling w i*‖f n i‖
  have hl i : Tendsto (fun n=>g n i) atTop (𝓝 (0:ℝ)) := by
    have hh : Tendsto (fun n=> F i* tuneS M (.some (m n)) i-F i*tuneS M none i) atTop (𝓝 (0:ℝ)) := by
      have hc := tendsto_const_nhds (x:=F i) (f:=atTop (α:=ℕ))
      simpa only [tuneS,sub_self] using ((hc.mul (stroke_late M (Row.rights _ _ J hv.le) m hp (i 0) (i (Fin.succ (0:Fin _))))).sub_const (F i * stroke M none (i 0) (i (Fin.succ (0:Fin _)))))
    simpa [g,f] using hh.norm.const_mul (ling w i)
  have hx n i : g n i ≤ (2*Q)*(ling w i*‖F i‖) := by
    have HH p : ‖tuneS M p i‖ ≤ Q := stroke_known M J hv.le ..
    apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le (F i*tuneS M (.some (m n)) i) (F i*tuneS M none i)) (ling_pos w i).le)
    simp only [norm_mul]
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (HH _) (norm_nonneg _)) (mul_le_mul_of_nonneg_left (HH _) (norm_nonneg _))) (ling_pos _ _).le); exact le_of_eq (by ring)
  have hh n i : 0≤g n i := mul_nonneg (ling_pos _ _).le (norm_nonneg _)
  have HM := tendsto_tsum_of_dominated_convergence (H.2.1.mul_left (2*Q)) hl (Eventually.of_forall (fun i j => (Real.norm_of_nonneg (hh i j)).trans_le (hx i j)))
  refine ⟨w,fun i=> ∑' j, g i j,hw,by simpa only [tsum_zero] using HM,fun i=>?_⟩
  simp only [he]; apply Charge.poolage _ (ling_one hw.le)
  have HE : Glow (f i) w (∑' j, g i j) := ⟨hh i,Summable.of_nonneg_of_le (hh i) (hx i) (H.2.1.mul_left (2*Q)),le_rfl⟩
  apply HE.mono (fun i=> (ling_pos _ _).le) _ le_rfl
  intro b; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ hw.le; exact_mod_cast (stems_le _).trans (stems_le b)
end YM.RG08
