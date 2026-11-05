import YM.RG08.Ratio.Cash
/-! # Triangular reset charges; rank two carried through same gate once -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Conductor
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect PowerSeries
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I : Type} {y δ η : I → ℝ}
variable {G : Gauge}{r : ℕ} (i : G.ColorIndex) (F : Air G)(Q : Pot G 2)

local notation "Ω" => compass i F

-- clean off field-independent and connection counterterm encountered exactly in degree two

def sifting (V : Pot G 2) := V-probeK i V • Q
lemma sifting_add {A B : Pot G 2} (h : Glows A) (he : Glows B) : sifting i Q (A+B)=sifting i Q A+sifting i Q B := by
  have H: Glows (A+B):=h.plus he; obtain ⟨w,X,hw,H⟩:=H; obtain ⟨v,p,hv,hA⟩:=h
  have hh:= probe_diff i H hA hw hv; rw [add_sub_cancel_left] at hh
  unfold sifting; rw [show probeK i (A+B)=probeK i A+probeK i B by rw [hh]; abel,add_smul]; abel
lemma sifting_sub {A B : Pot G 2} (h : Glows A) (he : Glows B) : sifting i Q (A-B)= sifting i Q A-sifting i Q B := by
  obtain ⟨w,X,hw,H⟩:=he; obtain ⟨v,p,hv,hA⟩:=h; unfold sifting; rw [probe_diff i hA H hv hw,sub_smul]; abel
lemma sifting_height {U : Pot G 2}{σ A B : ℝ} (h : Glow U σ A) (he : Glow Q σ B) (hp : 0<σ) :
    Glow (sifting i Q U) σ ((1+ probeFee G σ * B)*A) :=
  glow_less (h.sub (he.scale _) (fun i=>(ling_pos _ _).le)) le_rfl ((add_le_add (le_refl A) (mul_le_mul_of_nonneg_right (assesses i h hp) he.nonneg)).trans_eq (by ring))

def duetT (q : ℕ) := ∑ j∈range q, recitalR Ω (q+1) (j+1) • sifting i Q (sector Q F (j+1) 2)

lemma deuce (q : ℕ) (h : probeK i Q=1) : correct i F Q (2*(q+1)) 2=sifting i Q (F (2*(q+1)) 2)+ duetT i F Q q := by
  rw [correct_p _ _ _ (by decide) (by omega) (show 2*(q+1)+2=2+2*(q+1) from Nat.add_comm ..)]
  have hz := restored Ω (compass_zero ..) (q+1); rw [if_neg (by omega)] at hz
  let k:=recitalR Ω (q+1)
  let U j:= sector Q F j 2
  calc
     _ = ∑ j∈range (q+1+1), k j • (U j) := rfl
     _ = ∑ j∈range (q+1+1), k j • sifting i Q (U j) := by
      unfold sifting; simp_rw [smul_sub,Finset.sum_sub_distrib,smul_smul,show ∀ j,probeK i (U j)=Ω j from fun _=>(compass_eq i F Q h _).symm,← sum_smul]; rw [show (∑ j∈range (q+1+1),k j*Ω j)=0 from hz,zero_smul,sub_zero]
     _ = _ := by
      rw [sum_range_succ',show U 0= Q from sector_t ..,show sifting i Q Q=0 by unfold sifting; rw [h,one_smul,sub_self],smul_zero,add_zero]
      rw [sum_range_succ,show k (q+1)=1 from recital_priced Ω (compass_zero ..) _,one_smul]
      rw [show U (q+1)=F (2*(q+1)) 2 from sector_unique _ _ (by omega) (by decide) (by omega)]; exact add_comm ..

def eclat (q r : ℕ) := ∑ j∈range q, recitalR Ω q j • sector Q F j (r+3)
lemma tinder (q r : ℕ) : correct i F Q (r+1+2*q) (r+3)= F (r+1+2*q) (r+3) + eclat i F Q q r := by
  have hx : r+1+2*q+2=r+3+2*q:=by omega
  rw [correct_p _ _ _ (by omega) (by omega) hx,revise,sum_range_succ,sector_unique _ _ (by omega) (by omega) hx.symm,recital_priced Ω (compass_zero ..),one_smul]; exact add_comm ..

section billing
variable {T U : I→Air G} {P M : I→ Pot G 2}

lemma paired_cut (he : Audience y) (hp : ∀ i,0<η i) (h : Weighed y (fun i=> probeFee G (η i)))
    (hv : Both y δ P M η) {F H : I→ Pot G 2} (ht : Both y δ F H η) :
    Both y δ (fun j=> sifting i (P j) (F j)) (fun j=> sifting i (M j) (H j)) η := by
  exact ht.sub ((cost_probe i hp ht h).rangers hv he) he

-- application after raw and strict predecessors. k finite J obligations
lemma duetCharge (hc : Audience y)(hp : ∀ i, 0<η i)(hs : Weighed y (fun i=> probeFee G (η i)))
    (q : ℕ)(h : ∀ j, 0<j→ j≤ q → Both y δ (fun b=> T b (2*j) 2) (fun b=> U b (2*j) 2) η) (hH : Both y δ P M η) :
    Both y δ (fun j=> duetT i (T j) (P j) q) (fun j=> duetT i (U j) (M j) q) η := by
  let V (f:I→Air G) := fun j=> compass i (f j)
  have hv : ∀ l≤q,Lease y δ (fun j=> V T j l) (fun j=>V U j l) := by
    intro l hl; by_cases he:l=0
    · subst l; simp_rw [V,compass_zero]; exact Lease.const ..
    simp only [V,compass,he,if_false]; exact cost_probe i hp (h l (by omega) hl) hs
  unfold duetT; refine Both.list _ hc fun b hb=>?_ ; have hz:=mem_range.mp hb
  have hd := paired_cut i hc hp hs hH (h (b+1) (by omega) (by omega)) -- typo
  simp_rw [sector_unique (e:=2*(b+1)) _ _ (by omega) (by decide) (show 2+2*(b+1)=2*(b+1)+2 from Nat.add_comm ..)]
  exact Lease.rangers (Lease.rePrice (f:=V T) (g:=V U) hc hv (fun _=>compass_zero ..) (fun _=> compass_zero ..) (show q+1-(b+1) ≤ q by omega)) hd hc
lemma titanCharge (hc : Audience y)(hp : ∀ i, 0<η i)(hs : Weighed y (fun i=> probeFee G (η i)))
    (q r : ℕ)(h : ∀ j, 0<j→ j≤ q → Both y δ (fun b=> T b (2*j) 2) (fun b=> U b (2*j) 2) η)
    (hH : ∀ j<q, Both y δ (fun b=> T b (r+1+2*j) (r+3)) (fun b=>U b (r+1+2*j) (r+3)) η) :
    Both y δ (fun j=> eclat i (T j) (P j) q r) (fun j=> eclat i (U j) (M j) q r) η := by
  let V (f:I→Air G) := fun j=> compass i (f j)
  have hv : ∀ l≤q,Lease y δ (fun j=> V T j l) (fun j=>V U j l) := by
    intro l hl; by_cases he:l=0; · subst l; simp_rw [V,compass_zero]; exact Lease.const ..
    simp only [V,compass,he,if_false]; exact cost_probe i hp (h _ (by omega) hl) hs
  unfold eclat; refine Both.list _ hc fun b hb=> ?_
  simp_rw [sector_unique (e:=r+1+2*b) _ _ (by omega) (by omega) (show r+3+2*b = _ by omega)] -- can't infer _? 
  exact Lease.rangers (Lease.rePrice (f:=V T) (g:=V U) hc hv (fun _=>compass_zero ..) (fun _=> compass_zero ..) (show q-b ≤ q by omega)) (hH b (mem_range.mp hb)) hc
end billing
end YM.RG08.Conductor
