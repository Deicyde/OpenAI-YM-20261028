import YM.RG08.Vale.Sipper
/-!
# Assembling pol shells for arbitrary roots, repeated estimates
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{m L:Side}{A R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable {F: Labels.Frame G d} {T : SectionData F} {V : BoardU D R G}
variable {U : EnvelopeU D R G r}
-- T-test multi-linear value

def pass (U:EnvelopeU D R G r) (A:Fin r → Potential G)(φ:Exam D) := wallet (plug φ R ∘ U) (fun i=> deckP (A i))
lemma v_purse {A': Potential G}(hp:A'∈Place.rangeLt (Axis→G.Color) n) : ∃ C:ℝ,0≤C ∧ ∀ i,‖deckP A' i‖ ≤ C*dime n i.1 := by -- binder
  obtain ⟨C,h,H⟩:= Carrier.royalties n A' hp
  exact ⟨_,h,fun i=> (PiLp.norm_apply_le (A' (Place.seat i.1) (heap i).2) i.2.2).trans (H i.1 (heap i).2)⟩
lemma pocketbook (P:EnvelopeU D R G r)(hP:Polished P)(z:Fin r→ℕ)(A:Fin r→Potential G)(hp:∀ i,A i∈Place.rangeLt (Axis→G.Color) (z i))(φ:Exam D): Summable (fun b:Beads (Loc G 1) r=> P b (sheet D R φ)*∏ i,deckP (A i) (b i)) := by
  choose C hC H using fun i=> v_purse (hp i)
  let n:= ∑ i,z i
  have he (i : Fin r) (p: Fare G) : ‖deckP (A i) p‖≤ C i*dime n p.1:= (H i p).trans (mul_le_mul_of_nonneg_left (dime_more (single_le_sum (fun i _=> Nat.zero_le (z i)) (mem_univ i)) _) (hC i))
  exact (takes (polished_fun hP (plug φ R) n).choose_spec (fun i=>hC i) he).2.1.of_norm

def Abates (U:EnvelopeU D R G r) (d : ℕ) := ∀ (v:Fin r→Place.Potential G) (r':Fin r→ℕ), (∀ i,v i∈Place.rangeLt (Axis→G.Color) (r' i)) → ∀ (u:Cham), (∑ i,r' i)+cashT u < d→ pass U v (coinsT D u)=0
lemma held (H:Hol G)(h:Marvel τ V)(hp:Lank V)(ht:auditT H F V=0)(e j:ℕ): Abates (V e j) (d+1):= fun a v hw i hh=> shot H h hp ht i e j a v (Nat.le_of_lt_succ hh) hw
lemma banner (h:Abates U j)(hp:Polished U)(z:Fin r→ℕ)(x:Fin r→Potential G)(hx:∀ i,x i∈ Place.rangeLt (Axis→G.Color) (z i))(hv:(∑ i,z i)+t<j)(g:Exam D)(hT:g∈PaperT D t): pass U x g=0 := by
  induction hT using Submodule.span_induction with
  | mem i hi=> obtain ⟨u,hu,rfl⟩:= hi; exact h x z hx u ((Nat.add_le_add_left ((counted u).1 hu) _).trans_lt hv)
  | zero=> simp [pass,wallet,comp_apply,plug]
  | add a b _ _ ha hb=>
    have he w:= pocketbook U hp z x hx w
    refine Eq.trans (?_ : pass U x _=pass U x a+pass U x b) (by rw [ha,hb,add_zero]); unfold pass wallet
    simp only [comp_apply,plug,ContinuousLinearMap.apply_apply,map_add,_root_.add_apply,add_mul]; exact Summable.tsum_add (he _) (he _)
  | smul c a _ ha=>
    refine Eq.trans (?_ : pass U x _=c*pass U x a) (by rw [ha,mul_zero]); unfold pass wallet
    simp only [plug, map_smul, comp_apply,RingHom.id_apply]; change (∑' b,_)=_; -- should expose
    simp [mul_assoc,tsum_mul_left]

-- Flexible taps for interpolation expansion
abbrev partsP (d:ℕ)(k:Fin (d+1))(p:Site L)(Q:Cross L (Loc G 1) (Loc G 1)) : Paper (Loc G 1) (Loc G 1) := if k.val=d then remain d p Q else bud k.val p Q -- Cross not Precision?
lemma story (x : Fin (d+1))(hp : x.val < d)(Q:Cross L (Loc G 1) (Loc G 1))(p:Site L)(z:Fare G) :
    ∃ f∈ Place.rangeLt (Axis→G.Color) (x.val+1),deckP f=fun i=> partsP d x p Q i z := by
  let g (a:Axis)(k:G.ColorIndex) := Trellis.sector x.val (fun y=> node p Q (y,coord a,k) z)
  let f (x:E4)(i:Axis) : G.Color := WithLp.toLp 2 fun k=>g i k x
  have he (i): (fun y=> f y i)∈ Place.rangeLt G.Color (x.val+1) := by
    let T: (G.ColorIndex → ℝ) →L[ℝ] G.Color := (PiLp.continuousLinearEquiv (p:=2) ℝ (fun _:G.ColorIndex=>ℝ)).symm.toContinuousLinearMap
    exact Place.linear_band T _ (Place.vector_band (g i) (fun k=> Trellis.sector_band _ _)) -- order of args
  refine ⟨f,Place.vector_band _ he,?_⟩; funext i; unfold partsP; rw [if_neg hp.ne]
  unfold deckP f g bud; dsimp only; simp only [heap,← coord_map,axisEquiv.apply_symm_apply]; rfl

end YM.RG08.Vale
