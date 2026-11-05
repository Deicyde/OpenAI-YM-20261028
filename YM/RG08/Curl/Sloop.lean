import YM.RG08.Curl.Ship
/-! # Multi all-ages from existing stationary cost all ages, finite recursive.
Whole layout. No synthetic geometry discarded. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {A B C σ η : ℝ} {r s d n : ℕ}
variable {F : Atlas G}

lemma Foil.mono (h : Foil G F d σ C)(hp : 0<η)(he:η≤σ)(hx:C≤A): Foil G F d η A := ⟨_,fun i j=>(h.choose_spec.1 i j).mono hp he hx,h.choose_spec.2⟩
lemma foilPaid [NeZero r] (G : Gauge)(h:0<σ) (r' : ℕ)(_hr:r'=r) (n:ℕ) : ∃ η K, 0<η ∧ η ≤ σ ∧ 0 ≤ K ∧ ∀ (X:Skin G r)(A:ℝ),0≤ A → Mar X A σ → ∀ d:ℕ,d ≤ n→ Foil G (fun m=>turnSeries (m:=m) (Stationary.issue X)) d η (A*K) := by
  have he (k:ℕ):= orbit_cost G (r+1) k h
  choose w V hw hv H using he
  let y := Finset.range (n+1)
  let B k:= inkCost G r σ * V k
  have hh i : 0≤ B i:=mul_nonneg (inkCost_nonneg ..) (hv _)
  have hp : y.Nonempty:=⟨0,mem_range.mpr (by omega)⟩ -- incorrect
  let v:= min σ (y.inf' hp w); have ht : 0<v:= lt_min h ((Finset.lt_inf'_iff _).mpr (fun i hi=> hw _))
  refine ⟨v,∑ k∈ y,B k,ht,min_le_left ..,sum_nonneg (fun _ _=> hh _),fun X A hA hX d hx=>?_⟩
  have hu : d∈ y:= mem_range.mpr (by omega)
  obtain ⟨L,hL,hl⟩:= H d (Stationary.issue X) (A*inkCost G r σ) hX.pathways.1
  exact (show Foil G _ d _ (A* B d) from ⟨L,(by rw [show A*B d=A*inkCost G r σ* V d by rw [mul_assoc]]; exact hL),hl⟩).mono ht ((min_le_right ..).trans (Finset.inf'_le _ hu)) (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=> hh i) hu) hA)

abbrev Flotilla (G: Gauge) := (j:ℕ)→Skin G (j+1)
abbrev paint (K:Flotilla G)(m:Side)(i:ℕ) := turnSeries (m:=m) (Stationary.issue (K i))
abbrev embark (J p:ℕ) := Ico J (J+p)
def exalts (Z:Flotilla G) (s:Finset ℕ)(w C:ℝ):=∀ i∈s, Mar (Z i) C w
def shores (Z:Flotilla G)(s:Finset ℕ)(m:Side) := ∑ i∈s,paint Z m i
-- suffix starting at t≥1 (rank≥3). Foil support on all USED ranks
private lemma mingle (j p) : embark j (p+1)=insert j (embark (j+1) p):= Finset.ext fun i=> by simp only [embark,mem_insert,mem_Ico]; omega
private lemma transferSun {X : Skin G (r+1)} (hX : Mar X C σ)(hs:0<σ) : Pointwise (turnSeries (Stationary.issue X) (m:=m)) := stain_ink _ hs hX.pathways.1 hX.pathways.2

def Funds (F:Atlas G)(m j:ℕ)(w C:ℝ):= ∀ i∈embark m j,Foil G F (i+1) w C
lemma lightening (hσ:0<σ)(Z: Skin G (r+1))(A C w η K X:ℝ)(hC:0 ≤ A)(hz:Mar Z C σ)
    (V : Atlas G)(k n : ℕ)(hV : Funds V k n w A)(p : ∀ i,Pointwise (V i))
    (hP : ∀ i∈embark k n,Foil G (fun m=>turnSeries (Stationary.issue Z) (m:=m)) (i+1) η X) (hy:η ≤ w) (hp:0<η)(hh:A+X≤K): Funds (fun m=> V m-turnSeries (Stationary.issue Z)) k n η K := by
  intro i hi
  obtain ⟨f,H,hf⟩:= (hV i hi).mono hp hy le_rfl
  obtain ⟨g,he,hg⟩:=hP i hi
  exact (show Foil G _ _ η (A+X) from ⟨f-g,fun i j=> (H i j).sub (he i j),fun m=> Recorded.less (p _).analytic (transferSun hz hσ).analytic (hf m) (hg m)⟩).mono hp le_rfl hh
lemma splice_head (T:Flotilla G)(A:Skin G (r+1)) (p m) :
    shores (Function.update T r A) (embark r (p+1)) m= turnSeries (Stationary.issue A)+shores T (embark (r+1) p) m := by
  unfold shores paint; rw [mingle,sum_insert (by simp [embark]),update_self]; congr 1
  exact sum_congr rfl (fun i hi=> by rw [update_of_ne]; simp only [embark,mem_Ico] at hi; omega)
lemma pilots (G: Gauge)(n r:ℕ) (hR:1≤r) (h:0<σ): ∃ η C:ℝ, 0<η ∧ η≤σ ∧ 0≤C ∧ ∀ F:Atlas G,∀ K,0≤K → (∀ m, Pointwise (F m) ∧ Rays (r+2) (F m)) → Funds F r n σ K → ∃ T:Flotilla G, exalts T (embark r n) η (K*C) ∧ ∀ m, Rays (r+n+2) (F m-shores T (embark r n) m) := by
  induction n generalizing r σ with
  | zero=> refine ⟨σ,0,h,le_rfl,le_rfl,fun F K h hF _=>⟨0,(by simp [exalts,embark]),?_⟩⟩; simpa only [embark,Nat.add_zero,Ico_self,shores,sum_empty, sub_zero] using fun m=>(hF m).2
  | succ n ih=>
    obtain ⟨w,B,hp,hw,hB,H⟩:= currency G (r+1) (by omega) h
    obtain ⟨v,X,hv,h,hX,Hx⟩:= foilPaid G hp (r+1) rfl (r+1+n)
    obtain ⟨η,C,ht,hη,hC,H'⟩:= ih (r+1) (by omega) hv
    refine ⟨η,B+(1+B*X)*C,ht,(hη.trans h).trans hw,by positivity,fun F K hK hF hE=>?_⟩
    obtain ⟨A,hA,he⟩:= H F K hK hF (hE r (by simp [embark]))
    have hU:= Hx _ _ (mul_nonneg hK hB) hA
    let U m:= F m-turnSeries (Stationary.issue A)
    have hS : Funds U (r+1) n v (K*(1+B*X)):= by
      have ha : Funds F (r+1) n σ K:= fun i hi=> hE i (mingle r n ▸ mem_insert_of_mem hi)
      exact lightening hp A K _ _ _ _ _ hK hA F (r+1) n ha (fun m=>(hF m).1) (fun i hi=> hU _ (by simp [embark] at hi; omega)) (h.trans hw) hv (le_of_eq (by ring))
    obtain ⟨Z,hZ,HZ⟩:= H' U _ (by positivity) (fun m=> ⟨(hF m).1.sub (transferSun hA hp),he m⟩) hS
    refine ⟨Function.update Z r A,fun i hi=>?_,fun m=>?_⟩
    · rw [mingle,mem_insert] at hi; rcases hi with hx|hx; · subst i; rw [update_self]; exact hA.mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hK) (hη.trans h)
      rw [update_of_ne (by simp only [embark,mem_Ico] at hx; omega)]; exact (hZ i hx).mono (by nlinarith [mul_nonneg hK hB]) le_rfl
    rw [splice_head, show r+(n+1)+2=r+1+n+2 by omega]; convert HZ m using 1; unfold U; abel
end YM.RG08.Virtue
