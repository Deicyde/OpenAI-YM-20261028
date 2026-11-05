import YM.Next.RANK.ArcEstimate
import YM.Next.RANK.Rim

/-! Uniform finite measured errors relative to sampled free current.
We isolate them still in the Ledger at finite-order differences. This is NOT
an Estimate.Corrected/Arrays etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Prayer
open Configuration Beamer Function Lattice Wilson RG Value Normal Maxwell Wick Common CellsInt Labels
open scoped Topology Classical BigOperators

variable {G : Gauge} {n d k r M : ℕ} {V : Type*}

-- entries known real
lemma real_mapper (i : KeyIn G d) : ∀ j, star (mapper i j) = mapper i j := by
  intro j; unfold mapper
  simp [Finsupp.single_apply]
  apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
lemma real_frameX {x : Points n} (h : x∈conf _) (i j) : star ((frameX (G:=G) h).cov i j) = (frameX h).cov i j := by
  dsimp only [frameX]; split <;> simp [entry]

lemma integer (x : Points n) (h : x∈conf n) (d : ℕ) (p q) : (((currentX h G d).cov p q).re:ℂ) = (currentX h G d).cov p q := by
  have he (p : Fin n × KeyIn G d) z :
      let w := Normal.perSlot (fun _ : Fin n => mapper (d:=d) (G:=G)) p z
      star w=w := by
    intro z'
    -- mapping inj
    let f := Normal.perSlot (fun _ : Fin n => mapper (d:=d) (G:=G)) p
    by_cases hp : z.1=p.1
    · rw [show z'=mapper p.2 z.2 by
        dsimp only [z',perSlot]; nth_rw 1 [show z=(p.1,z.2) from Prod.ext hp rfl]; exact Finsupp.mapDomain_apply (fun i j h => Prod.mk.inj h |>.2) _ _]
      exact real_mapper ..
    have hz : f z=0 := by
      by_contra h; have hu := Finsupp.mem_support_iff.mpr h
      obtain ⟨a,b,c⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hu); exact hp (congr_arg Prod.fst c.symm)
    change star (f z)=f z; simp [hz]
  have hs : star ((currentX h G d).cov p q)=(currentX h G d).cov p q := by
    unfold currentX Normal.scope treats
    simp_rw [Finsupp.linearCombination_apply,Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [star_sum, star_mul', real_frameX, he]
  exact Complex.conj_eq_iff_re.mp hs

variable {x : Points n} (hx : x∈conf n) (d)

def collect (r : ℝ) (G : Gauge) (i j : Fin n) : Bridge G := arc d r (fun a b => ((currentX hx G d).cov (i,a) (j,b)).re)

-- Bridges here are after orienting the endpoint coefficients to the original W-cumulant frame.

variable {ρ P B E e : ℝ}
structure Meridian (T X ε B e ρ : ℝ) (M : ℕ) : Prop where
  aperture : 1≤ρ
  sure : 0 ≤ T
  small : 0 ≤ X
  fine : 0 ≤ ε
  vertical : 1 ≤ B
  origin : sensed (G:=G) d T
  debris : ((M:ℝ))^(d-1) ≤ T
  rapid : X*T ≤ B
  precision : ε*T*T ≤ e
  precise : ε*T ≤ e
  spoke i j : ‖(currentX hx G d).cov i j‖ + X*T*T ≤ B
  full : X*T*T ≤ B

variable (R T s : ℝ) (Y : Meridian (G:=G) d hx T P E B e R M) (f : V → Address G)
variable (H : ∀ i, street (f i).1 ≤ M)
variable (Γ : Fin n → Fin n → Bridge G) (μ : Fin n → Horizon G) (h : ∀ i j x y, Γ i j x y=Γ j i y x)

structure Reads (M : ℕ) (P E : ℝ) : Prop where
  confirms i : Gather d R P M (μ i) ∧ Drift d R E (μ i)
  rows i j : Vane G d R P E M (Γ i j-collect d hx R G i j)

include Y H
lemma resolution (X : Reads (G:=G) d hx R Γ μ M P E) :
    let u := primary d f R Γ h
    let m := seen d f R μ
    let F := currentX hx G d
    Sorts u m B ∧ Nearby (Particle.ferry u) F (m∘ Particle.polar) 0 B e := by
  intro u m F
  let σ := passcode f R d
  have hs := Y.aperture
  have hg i : ‖m i‖ ≤ B := by
    refine le_trans (le_of_eq (Complex.norm_real _)) ?_
    exact (flight f hs Y.small H Y.debris Y.origin (X.confirms i.1).1 i.2).trans Y.rapid
  let L : Fin n → Fin n → Bridge G := collect d hx R G
  have he (i j : Fin n × (KeyIn G d ⊕ V)) : ‖mourn (σ i.2) (σ j.2) ((Γ (i.1:Fin n) j.1)-L i.1 j.1)‖ ≤ P*T*T := eastward f (X.rows i.1 j.1) hs Y.small H Y.debris Y.origin _ _
  have hp : Sorts u m B := by
    refine ⟨Y.vertical,hg,?_⟩
    intro i j
    let C := Γ i.1 j.1-L i.1 j.1
    calc
      _ = ‖mourn (σ i.2) (σ j.2) (Γ i.1 j.1)‖ := Complex.norm_real _
      _ ≤ ‖mourn (σ i.2) (σ j.2) (L i.1 j.1)‖ + P*T*T := by
        rw [show Γ i.1 j.1=L i.1 j.1+C from (by unfold C; abel),map_add]; exact (norm_add_le _ _).trans (add_le_add_right (he i j) _)
      _ ≤ _ := by
        rw [show mourn (σ i.2) (σ j.2) (L i.1 j.1)=_ from exact_fee d f R _ i.2 j.2 (zero_lt_one.trans_le hs)]
        obtain ⟨i,I|I⟩ := i <;> obtain ⟨j,J|J⟩ := j <;> simp <;> first | exact Y.full | skip
        rw [← Real.norm_eq_abs, ← Complex.norm_real, integer]; exact Y.spoke _ _
  let f' := Particle.polar (A:=Fin n) (V:=KeyIn G d) (W:=V)
  let Q := Particle.ferry u
  have ha (i j : Fin n × KeyIn G d) : Q.cov i j = u.cov (f' i) (f' j) := match_name ..
  refine ⟨hp,⟨⟨Y.vertical,fun i => hg _,fun i j => ha i j ▸ hp.entries _ _⟩,?_, (mul_nonneg Y.fine Y.sure).trans Y.precise,?_,?_⟩⟩
  · refine ⟨Y.vertical,fun i => by simpa using zero_le_one.trans Y.vertical,fun i j => ?_⟩
    linarith only [Y.spoke i j,mul_nonneg (mul_nonneg Y.small Y.sure) Y.sure]
  · intro i; rw [Pi.zero_apply,sub_zero]; apply le_trans _ Y.precise; change ‖m _‖ ≤ _
    exact le_trans (le_of_eq (Complex.norm_real _)) (fares f hs E Y.fine (μ i.1) i.2 T Y.origin (X.confirms _).2)
  rintro ⟨i,a⟩ ⟨j,b⟩; let I := (i,a); let J := (j,b); let v := σ (.inl a); let w := σ (.inl b)
  have hv : (u.cov (f' I) (f' J)) = ((mourn v w (Γ i j)):ℂ) := rfl
  have hw : F.cov I J=((mourn v w (L i j)):ℂ) := by
    rw [show mourn v w (L i j)= _ from exact_fee d f R _ (.inl a) (.inl b) (zero_lt_one.trans_le hs)]; simp; exact (integer ..).symm
  change ‖Q.cov I J-F.cov I J‖≤ e; rw [ha,hw,hv,← Complex.ofReal_sub,Complex.norm_real,← map_sub]; exact (starbound f (X.rows i j) hs Y.fine Y.sure Y.origin ..).trans Y.precision
end YM.Next.Rank.Prayer
