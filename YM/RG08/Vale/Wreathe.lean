import YM.RG08.Vale.Pennant
/-!
# Sum whole polynomial subtractions on the cover.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter Matrix
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {S ξ Υ R A B z:ℝ} {d D m r h:ℕ} {L c f:Side} {V:EnvelopeU D R G r}
variable {X:Cross L (Loc G 1) (Loc G 1)} {F K : Cover × Loc G 1 → ℝ} {w : Site L}
-- Assembled preimage. factor engineering from actual scale passed afterwards

def halo (p:Site L)(V:EnvelopeU D R G r)(Q:Cross L (Loc G 1) (Loc G 1)): EnvelopeU D R G r := belly p Q (fun b=> Shade.readdress (V b) p)
variable (hw:Odd L.val)(hp:1/2≤R)(hz:d+1≤D)
def plate (p:Site L) : Sight D R→L[ℝ] Sight D R := Scores.Pages.scroll (spinner p) _ _ (nesting p hw hp)
def chest (p:Site L)(i: Fin ((d+1)+1)) : Sight D R→L[ℝ] Sight D R:=
    if h:i.val=d+1 then plate hw hp p - padded (nesting p hw hp) hz else
      height L i.val • mirror (nesting p hw hp).here (show i.val ≤ D by omega)
lemma chest_all (p:Site L) : plate (D:=D) hw hp p=∑ i : Fin (d+1+1),chest hw hp hz p i := by
  rw [Fin.sum_univ_castSucc]; unfold chest; rw [dif_pos (Fin.val_last (d+1)), show (∑ i:Fin (d+1),_) = padded (nesting p hw hp) hz from ?_]; abel
  apply Finset.sum_congr rfl; intro k _; rw [dif_neg]; rfl
  exact k.isLt.ne
omit hw in
lemma chest_income (d k D : ℕ)(h:d+1=k)(hz:k≤D)(R:ℝ)(hp:1/2≤R) : ∃ A:ℝ,1≤A∧ ∀ (L:Side)(p:Site L)(hw:Odd L.val)(i:Fin (d+1+1)), ‖chest hw hp (h.symm ▸ hz) p i‖≤ A*height L i.val := by
  subst k
  obtain ⟨C,hc,H⟩:=refrain hz R
  let f (i:Fin (d+1+1)):=‖planL D i.val R‖*((i.val.factorial:ℝ)⁻¹*(4:ℝ)^i.val)
  let A:=C+∑ i,f i; have hp' i : 0 ≤ f i := by unfold f; positivity
  have hA:C≤A := le_add_of_nonneg_right (sum_nonneg fun i _=> hp' i)
  refine ⟨A,hc.trans hA,fun L p hw i=>?_⟩
  unfold chest; split
  next hi=>
    rw [hi]; exact (H _ _ _).trans (mul_le_mul_of_nonneg_right hA (height_p ..).le)
  next hi=>
    rw [norm_smul,Real.norm_of_nonneg (height_p ..).le,mul_comm]
    refine mul_le_mul_of_nonneg_right ((mirror_rule ..).1.trans ?_) (height_p ..).le
    exact (single_le_sum (fun i _=> hp' i) (mem_univ i)).trans (le_add_of_nonneg_left (zero_le_one.trans hc))
lemma chest_test (p:Site L)(i:Fin (d+1+1))(g:Exam D) (he:i.val<d+1) : ∃ φ∈ PaperT D i.val,chest hw hp hz p i (sheet D R g)=sheet D R φ := by
  refine ⟨height L i.val • Pages.crop (spinner p) g i.val, Submodule.smul_mem _ _ (tensorT _),?_⟩
  rw [chest,dif_neg he.ne,_root_.smul_apply,(mirror_rule ..).2,map_smul]
-- decomposition lid

def whirl (p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(V:EnvelopeU D R G r)(x:Fin (d+1+1))(v: Fin r→ Fin (d+1))(a:Beads (Loc G 1) r × Beads (Loc G 1) r) : Voice D R:=sires (fun i=>(V i).comp (chest hw hp hz p x)) (bulb (fun i=> partsP d (v i) p Q)) a
def vanish (p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(V:EnvelopeU D R G r)(x: Fin (d+1+1))(v: Fin r→ Fin (d+1)) := revolve (fun i=>(V i).comp (chest hw hp hz p x)) (fun i=> partsP d (v i) p Q)
lemma parts_all (d:ℕ)(p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(i a): ∑ n:Fin (d+1),partsP d n p Q i a=node p Q i a := by
  rw [Fin.sum_univ_castSucc]; unfold partsP; rw [if_pos (Fin.val_last d), buds_sum d]; rw [Pi.add_apply,Finset.sum_apply]; congr 1; rw [← Fin.sum_univ_eq_sum_range]; apply sum_congr rfl; intro i hi; rw [if_neg (show i.castSucc.val ≠ d from i.isLt.ne)]; rfl
lemma whirling (p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(V:EnvelopeU D R G r)(a: Beads (Loc G 1) r× Beads (Loc G 1) r) :
    sires (fun i=> Shade.readdress (V i) p) (bulb (fun _:Fin r=> node p Q)) a=∑ i : Fin (d+1+1),∑ z : Fin r→Fin (d+1), whirl hw hp hz p Q V i z a := by
  unfold sires; dsimp only; rw [show Shade.readdress (V a.1) p=(V a.1).comp (plate hw hp p) from dif_pos ⟨hw,hp⟩,chest_all hw hp hz,show bulb (fun _ : Fin r=> node p Q) a=∑ z:Fin r→ Fin (d+1),bulb (fun i=> partsP d (z i) p Q) a from ?_]
  · rw [show (V a.1).comp (∑ i,chest hw hp hz p i)=∑ i,(V a.1).comp (chest hw hp hz p i) from ?_,Finset.smul_sum]
    · exact sum_congr rfl fun i _=> sum_smul ..
    ext q; simp [_root_.sum_apply]
  unfold bulb; simp_rw [← parts_all d p Q]; exact Fintype.prod_sum ..
lemma whirl_pen {p:Site L} (hv : ∀ i:Fin (d+1+1),∀ z:Fin r→Fin (d+1), Quire.Pens (whirl hw hp hz p X V i z)) :
    halo p V X= ∑ i:Fin (d+1+1),∑ z: Fin r→Fin (d+1), vanish hw hp hz p X V i z := by
  funext t; unfold halo belly revolve; simp_rw [whirling hw hp hz,Finset.sum_apply]
  have he i z: Summable (fun j=> whirl hw hp hz p X V i z (j,t)):= (hv i z).of_norm.prod_symm.prod_factor t
  rw [Summable.tsum_finsetSum (fun i _=> summable_sum (s:=univ) (fun z _=> he i z))]; apply sum_congr rfl; intro i _; exact Summable.tsum_finsetSum (fun z _=> he i z)

def burden (i:Fin (d+1+1))(x : Fin r→Fin (d+1)) := i.val+∑ j, ((x j).val+1)
lemma whirled (h:Abates V (d+1))(hV:Polished V) (p:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(x:Fin (d+1+1))(v:Fin r→Fin (d+1))(he:burden x v≤d) (hv : Pens (whirl hw hp hz p Q V x v)): vanish hw hp hz p Q V x v=0 := by
  funext i; ext b
  obtain ⟨g,rfl⟩:=doors D R b
  unfold burden at he; obtain ⟨φ,hφ,hT⟩:= chest_test hw hp hz p x g (by omega)
  have hs j : (v j).val<d := by
    have hn := single_le_sum (fun j _=> Nat.zero_le ((v j).val+1)) (mem_univ j); omega
  choose f hF H using fun j=> story _ (hs j) Q p (i j)
  change plug g R (∑' j,whirl hw hp hz p Q V x v (j,i))=0
  rw [(plug g R).map_tsum (show Summable (fun j=> whirl hw hp hz p Q V x v (j,i)) from hv.of_norm.prod_symm.prod_factor i)]
  have hp: (∑ k,((v k).val+1))+x.val < d+1 := by omega
  apply Eq.trans _ (banner h hV _ _ hF hp φ hφ)
  unfold pass wallet; apply tsum_congr; intro j
  unfold whirl sires bulb; rw [map_smul]; change _ * (V j) (chest hw _ hz p x (sheet D R g))= V j (sheet D R φ) * _; rw [hT,mul_comm]; congr 1; apply prod_congr rfl; intro k _; exact (congr_fun (H k) (j k)).symm
end YM.RG08.Vale
