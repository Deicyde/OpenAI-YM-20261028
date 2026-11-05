import YM.RG08.Vale.Album
/-! # Full algebraic cancellation in radial tests. For the complete
null projection NOT assuming individual rank pieces transverse. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators
variable {E α:Type} {G:Gauge} {d D i j k r n τ u m e : ℕ} {R:ℝ} {F : Labels.Frame G d} {V : BoardU D R G}
lemma basin_sums {a:E→Plume G d j}(s: Finset E): basin (∑ i∈s,a i)=∑ i∈s,basin (a i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty,sum_empty]; exact basin_zero _ rfl
  | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,basin_add,ih]
set_option maxHeartbeats 500000 in
lemma ply {M:Plume G d j}{ν:Cham}(H: ∀ (b:F.Index),(F.grades b).2=j→ (F.grades b).1+cashT ν≤d→ F.coords (basin M) b=0)
  (A:Fin j→ Snap G d)(w : Fin j→ ℕ)(hv: ∀ i, Place.throughSlot (A i) (w i))(hw:(∑ i,w i)+cashT ν≤ d)(he:j≤d): M.val A=0 := by
  let p:= basin M
  have hx k (hk:k+cashT ν≤d): gradePart (k,j) p=0 := by
    apply F.coords.injective; rw [map_zero]; ext1 i
    by_cases hh : (k,j)=(F.grades i)
    · rw [hh,← Film.costs_only]; exact H i (congr_arg Prod.snd hh.symm) ((congr_arg (fun b=>b.1+cashT ν) hh).symm.trans_le hk)
    exact F.power_coefficient i hh (gradePart_mem ..)
  let B (i : Fin j) (k:Fin (d-1)) : Snap G d := Pi.single k (A i k)
  have hg : ∀ b:Fin j → Fin (d-1), M.val (fun i=>B i (b i))=0 := by
    intro b; by_cases H : ∀ i,(b i).val+2≤ w i
    · have h' : Parts.rate b+cashT ν≤d:= (Nat.add_le_add_right (sum_le_sum fun i _=>H i) _).trans hw
      have ht : WardBin.tile (shadeC M) (Parts.rate b)=0 := by
        have hf:= basin_tile M (le_trans (Nat.le_add_right _ _) h') he
        -- specify k=j
        have hp: gradePart (Parts.rate b,j) (basin M)=0:= hx _ h'
        simpa [hp] using hf.symm
      have hS : shadeC M (fun i=>B i (b i))=0 := Parts.tile_detects (shadeC M) (shade_sym _) b ht (fun i => A i _)
      rw [shade_all] at hS; simpa [mul_eq_zero,Nat.factorial_ne_zero] using hS
    push Not at H; obtain ⟨i,hi⟩:=H; exact M.val.map_coord_zero i (by simp [B,hv i _ hi])
  rw [show A=(fun i=> ∑ k,B i k) from funext fun i=> (Finset.univ_sum_single _).symm,M.val.map_sum B]; exact sum_eq_zero fun b _=>hg b
lemma roundTrip (h:Marvel τ V)(φ:Exam D) : Dappled (Loom.strand τ i (fun a b=>plug φ R ∘ V a b) r) := strand_dapple (fun i j=>Tidy.map _ (h.hem i j)) (fun m=> h.wardrobe m φ 0)
-- Cost qualification is joint.
lemma plot (H:Hol G)(p:Marvel τ V) (hp:Lank V)(hq:auditT H F V=0)(g:Cham) (n:ℕ)
    (X:Fin j→ Snap G d)(a:Fin j→ℕ)(ha: ∀ i,Place.throughSlot (X i) (a i)) (hv : (∑ i,a i)+cashT g ≤ d)(hj:j≤d) :
    (∑ i∈range (j+1), vault (Loom.strand τ n (fun j r=> plug (coinsT D g) R ∘ V j r) i) (screenR G d) X)=0 := by
  let W i:=Loom.strand τ n (fun j r=> plug (coinsT D g) R ∘ V j r) i; let C (i:ℕ):= cook (V:=W i) (roundTrip p (φ:=coinsT D g)) (strandP hp (coinsT D g)) H d j
  let M:=∑ i∈range (j+1),C i
  have h (i:ℕ): vault (W i) (screenR G d) X=(C i).val X := (penny_amt (roundTrip p _).toTidy (strandP hp _) _).symm
  have he : ∀ (b:F.Index),(F.grades b).2=j→ (F.grades b).1+cashT g ≤ d → F.coords (basin M) b=0 := by
    intro b hb hd
    let B:Letter F:= ⟨b,g,hd⟩
    have ht : ∀ i, ladle H (W i) d j = basin (C i):= fun i=> dif_pos (And.intro (roundTrip p _) (strandP hp _))
    unfold M; rw [basin_sums]; simp_rw [← ht]; rw [← show slot B=j from hb]
    change F.coords _ B.label=_; unfold W; change F.coords _ B.label=0
    have ht := audit_tile (i:=n) H p hp B; rw [hq] at ht
    exact ht.trans (by simp)
  exact ((sum_congr rfl fun i _=> h i).trans (by unfold M; rw [AddSubmonoidClass.coe_finsetSum,_root_.sum_apply] : _= M.val X)).trans (ply he X a ha hv hj)

end YM.RG08.Vale
