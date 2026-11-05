import YM.TraceExtension.Fock.RealTests

/-! Remove the transverse projectors in the locality test using membership in
the Fock space; no assumption about Lorentz invariance of the embedding. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {m n : ℕ}

def mail (i : Fin n) (s : Tags m n) (j : SpaceAxis) := update s i ((s i).1,j)
def mailbox (i : Fin n) : Equiv.Perm (Tags m n × SpaceAxis) where
    toFun a := (mail i a.1 a.2,(a.1 i).2)
    invFun a := (mail i a.1 a.2,(a.1 i).2)
    left_inv := fun ⟨s,t⟩ => by apply Prod.ext <;> simp [mail]
    right_inv := fun ⟨s,t⟩ => by apply Prod.ext <;> simp [mail]

private def mixed (x : Ambient m) (g : Fin n→ TestList m) (u : Finset (Fin n)) (p : Mom n) (s : Tags m n) :=
    star (sectionFn x ⟨n,s⟩ p) * ∏ j : Fin n, if j∈u then testPhoton (g j) (s j) (p j) else rawPhoton (g j) (s j) (p j)
private lemma mixed_eq (x : Ambient m) (hp : PhysicalWave x) (g : Fin n→ TestList m) (u : Finset (Fin n)) {i : Fin n} (hi : i∉u) :
    ∀ᵐ p∂photons n, (∑ s, mixed x g (insert i u) p s) = ∑ s, mixed x g u p s := by
    filter_upwards [ae_all_iff.mpr (fun t => hp.projects n t i)] with p he
    let T (s : Tags m n) := star (sectionFn x ⟨n,s⟩ p); let G (s : Tags m n) := rawPhoton (g i) (s i) (p i)
    let V (s : Tags m n) := ∏ j ∈ (Finset.univ.erase i), if j ∈ u then testPhoton (g j) (s j) (p j) else rawPhoton (g j) (s j) (p j)
    let P := polarization (p i)
    have hT (s) : T s = ∑ k : SpaceAxis,P (s i).2 k*T (mail i s k) := by
        unfold T P sectionFn; nth_rw 1 [he s]; simp only [star_sum,star_mul,pol_real,mul_comm]; rfl
    have hm (s) : mixed x g u p s = ∑ k : SpaceAxis,(P (s i).2 k*T (mail i s k))*(G s*V s) := by
        unfold mixed; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_neg hi, ← Finset.sum_mul, ← hT]
    have hw (s) : mixed x g (insert i u) p s= ∑ k : SpaceAxis,(P (s i).2 k*T s)*(G (mail i s k)*V s) := by
        unfold mixed; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos (Finset.mem_insert_self ..)]
        have hV : V s = ∏ j∈ (Finset.univ.erase i), if j∈insert i u then testPhoton (g j) (s j) (p j) else rawPhoton (g j) (s j) (p j) := by
            apply Finset.prod_congr rfl; intro j hj; simp [(Finset.mem_erase.mp hj).1]
        rw [← hV]; unfold testPhoton
        rw [Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
        dsimp only [G,mail,P,T]; rw [update_self]; ring
    have hV (s k) : V (mail i s k)=V s := Finset.prod_congr rfl fun j hj => by simp only [mail,update_of_ne (Finset.ne_of_mem_erase hj)]
    let Y := fun v : Tags m n × SpaceAxis => (P (v.1 i).2 v.2*T v.1)*(G (mail i v.1 v.2)*V v.1)
    simp_rw [hm,hw]
    rw [← Fintype.sum_prod_type Y]; rw [← Equiv.sum_comp (mailbox (m:=m) i) Y,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro s hs
    apply Finset.sum_congr rfl; intro k hk
    change (P (mail i s k i).2 (s i).2*T (mail i s k))*(G (mail i (mail i s k) (s i).2)*V (mail i s k))=_
    rw [hV]; simp [mail, P, pol_symm (p i) k (s i).2]
private lemma pure_ae (x : Ambient m) (hp : PhysicalWave x) (g : Fin n→TestList m) : ∀ᵐ p∂photons n,
    (∑ s, star (sectionFn x ⟨n,s⟩ p)*pureTest g s p) = ∑ s, star (sectionFn x ⟨n,s⟩ p) * ∏ i, rawPhoton (g i) (s i) (p i) := by
    have he (u : Finset (Fin n)) : ∀ᵐ p ∂photons n,(∑ s, mixed x g u p s)= ∑ s, mixed x g ∅ p s := by
        induction u using Finset.induction_on with
        | empty => simp
        | insert i s h hs => filter_upwards [mixed_eq x hp g _ h,hs] with p hi hj using hi.trans hj
    simpa only [mixed,Finset.mem_univ,Finset.notMem_empty,↓reduceIte,pureTest] using he Finset.univ
lemma raw_earlier (x : Ambient m) (hp : PhysicalWave x) (g : Fin n→ TestList m) : earlier g x =
    ∫ p, ∑ s, star (sectionFn x ⟨n,s⟩ p) * ∏ i, rawPhoton (g i) (s i) (p i) ∂photons n := by
    unfold earlier; rw [← integral_finsetSum]; exact integral_congr_ae (pure_ae x hp g)
    exact fun i _ => product_int (wave_lp x ⟨n,i⟩) (pure_lp g i)

def singleTest (s : Label m) (f : Test4) : TestList m := Pi.single s f
lemma picked (x : Ambient m) (hp : PhysicalWave x) (s : Tags m n) (f : Fin n → Test4) :
    earlier (fun i => singleTest (s i) (f i)) x = ∫ p, star (sectionFn x ⟨n,s⟩ p)*∏ i, (‖p i‖:ℂ)*testPlus (f i) (momentum (p i)) ∂photons n := by
    rw [raw_earlier x hp]; apply integral_congr_ae; filter_upwards with p
    rw [Finset.sum_eq_single_of_mem s (Finset.mem_univ _)]
    · simp only [rawPhoton,singleTest,Pi.single_eq_same,Complex.real_smul]
    intro t ht hn
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hn; rw [Finset.prod_eq_zero (Finset.mem_univ i),mul_zero]
    simp [rawPhoton,singleTest,Pi.single_eq_of_ne hi]

lemma bar_hat (f : Probe E4) (p : E4) : star (testPlus (Probe.bar f) p) = Probe.hat f p := by
    rw [testPlus_apply, Probe.hat_eq, Complex.star_def,← integral_conj]
    congr! 1; ext x; simp [Probe.plane_inverse]
lemma single_bar (s : Label m) (f : Test4) : barList (singleTest s f)=singleTest s (Probe.bar f) := by
    ext i; by_cases h:i=s <;> simp [h,singleTest,barList, Pi.single_eq_of_ne]

lemma positioned (f : Test4) (x y : Ambient m) (p : PhysicalWave x) (q : PhysicalWave y) (h : OnVac f x y)
    (s : Tags m n) (g : Fin n→ Test4) (hc : ∀ i, HasCompactSupport ⇑(g i)) (hd : ∀ i, Fields.causal f (g i)) :
    (∫ w, sectionFn x ⟨n,s⟩ w*∏ i,(↑‖w i‖:ℂ)*Probe.hat (g i) (momentum (w i)) ∂photons n) =
      ∫ w, star (sectionFn y ⟨n,s⟩ w)*∏ i, (↑‖w i‖:ℂ)*testPlus (g i) (momentum (w i)) ∂photons n := by
    have he (i : Fin n) : singleTest (s i) (g i)∈localized m f := by
        intro j; by_cases hp:j=s i
        · subst j; rw [singleTest, Pi.single_eq_same]; exact ⟨hc i,hd i⟩
        rw [singleTest,Pi.single_eq_of_ne hp]; exact (localized m f).zero_mem j
    have hh := sectors_local f x y p q h (fun i => singleTest (s i) (g i)) he
    simp only [Function.comp_def,single_bar] at hh; rw [picked x p, picked y q, Complex.star_def,← integral_conj] at hh
    refine Eq.trans ?_ hh; apply integral_congr_ae; filter_upwards with i
    simp only [map_mul,map_prod, ← Complex.star_def, bar_hat, star_star]; simp
end YM.TraceExtension.Photons
