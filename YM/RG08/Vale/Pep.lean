import YM.RG08.Vale.Pipers
/-!
# Coordinate cost preservation without donating another displacement
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {S ξ Υ R A B z:ℝ} {d D m j r h:ℕ} {L c f:Side} {V:EnvelopeU D R G r}
variable {X:Cross L (Loc G 1) (Loc G 1)} {p: Site L}
lemma halo_ear {w:Fare G→ℝ} {v:Fare G→ℝ}(he:Odd L.val)(h:1/2≤R)(hz:1≤w)(hv:1≤v)(p:Site L)
    (hP:0≤A)(hp:∀ i,Charge v (node p X i) (A*w i))(hf : Quire.Ink (brocade w) V B):
    Quire.Ink (brocade v) (halo p V X) (A^r*B) := by
  have hX : Quire.Ink (brocade w) (fun i=> readdress (V i) p) B := budget_mono hf
      (fun i=> mul_nonneg ((fineBro hz i).trans' zero_le_one) (norm_nonneg _)) (fun i=> mul_le_mul_of_nonneg_left (read_scores he h p _).1 ((fineBro hz i).trans' zero_le_one))
  simpa only [halo, belly,prod_const,card_univ,Fintype.card_fin] using revolves (P:=fun i=>node p X) hX (p:=fun _:Fin r=>A) (fun i=>hP) (fun i=>hp) hv
lemma halo_all (he:Odd L.val)(h:1/2≤R)(hz:Whole X)(hp:Site L)(hV:Polished V) : Polished (halo hp V X):= by
  intro k; obtain ⟨C,hp'⟩:= hV k; obtain ⟨B,hB,hh⟩:=nodes_budget _ hz k
  exact ⟨_,halo_ear he h rug_one rug_one hp hB (hh hp) hp'⟩
lemma all_aboard (he:Odd L.val)(h:1/2≤R)(hz:Whole X)(hV:Polished V) : Polished (aboard m X V) := polished_scale (polished_sum (fun i _=>halo_all he h hz i hV)) _
lemma halo_one (he:Odd L.val)(h:1/2≤R)(hp:Whole X)(ht:Tidy V)(i:Site L)(φ:Exam D): plug φ R∘halo i V X=belly i X (plug (Scores.Pages.roll (spinner i) (Carrier.unitStep L) φ) R∘V) := by -- f unused
  let W b:= readdress (V b) i; have hh: Tidy W:= ⟨rays_print ht.pens h he i,fun _ j=> congr_arg (fun z=> readdress z i) (ht.woven ..)⟩
  unfold halo; rw [belly_sound _ i hp hh]; congr 1; exact funext fun b=> (read_scores he h i _).2 φ
lemma halo_poly (he:Odd L.val)(h:1/2≤R)(hp:Whole X)(ht:Tidy V)(hV:Polished V)(p:Site L)(φ:Exam D)
    (x:Fin r→Potential G) (z:ℕ)(hx:∀ i,x i∈rangeLt _ z): pass (halo p V X) x φ=
    wallet (plug (Scores.Pages.roll (spinner p) (Carrier.unitStep L) φ) R∘V) (fun i=> pursed (node p X) (deckP (x i))) := by
  let g:=Scores.Pages.roll (spinner p) (Carrier.unitStep L) φ; let F:= plug g R∘V; have hv : Polished F := polished_fun hV _
  unfold pass; rw [halo_one he h hp ht]; obtain ⟨C,hC,H⟩:= nodes_budget _ hp z; choose A hA hh using fun i=> v_purse (hx i)
  exact divulge (w:=rug z) (p:=fun _:Fin r=> C) (hv z).choose_spec (fun _=>H p) (fun _=>hC) rug_one _ _ (fun i=> hA i) hh

-- linear carry
lemma scaled_band {n':ℕ} {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{u:E4→E} (h:u∈rangeLt E n') (c:ℝ) : (fun z:E4=> u (c•z))∈ rangeLt E n' := by -- variable
  induction n' generalizing u with
  | zero=> rw [rangeLt,Submodule.mem_bot] at h; rw [h]; exact Submodule.zero_mem _
  | succ n ih=>
    rw [rangeLt_succ] at h; obtain ⟨p,hp,q,hq,rfl⟩:= Submodule.mem_sup.mp h
    exact Submodule.add_mem _ (show (fun z=> p (c • z)) ∈rangeLt E (n+1) from by simp_rw [exact_scale hp]; exact Submodule.smul_mem _ _ (exact_le_band (Nat.lt_succ_self _) hp)) (grows _ (Nat.le_succ n) (ih hq)) -- remove arg
lemma roll_band (d:Cham)(x:E4)(c:ℝ): Scores.Pages.roll x c (coinsT D d)∈ PaperT D (cashT d) := by
    apply passT; change (fun z=>beck d (x+c • z))∈_; simp_rw [add_comm x]; exact scaled_band (u:=fun z=> beck d (z+x)) (Place.band_shift (exact_le_band (Nat.lt_succ_self _) (page_poly d)) x) _
lemma roll_only (u:Cham)(x:E4)(c:ℝ): let p:=coinsT D u; (Scores.Pages.roll x c p-c^(cashT u) • p).val∈ rangeLt ℝ (cashT u) := by
  intro b; have ht:= scaled_band (Place.band_step (exact_le_band (Nat.lt_succ_self _) (page_poly u)) x) c
  change (fun z:E4=> beck u (x+c•z)-c^(cashT u)*beck u z) ∈ _
  convert ht using 1; ext z; rw [add_comm, exact_scale (page_poly u)]; rfl
end YM.RG08.Vale
