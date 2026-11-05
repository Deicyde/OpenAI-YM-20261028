import YM.TraceExtension.Fock.Coefficients

/-! Polarized comparison for all real & complex electric test arrays in
spacelike complement of the field smearing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {m n : ℕ}

abbrev CLinear := MultilinearMap ℂ (fun _ : Fin n => TestList m) ℂ

def testFunctional (j : Label m) (p : Space3) : TestList m →ₗ[ℂ] ℂ := IsLinearMap.mk' (fun h => testPhoton h j p)
    ⟨fun i k => photon_add i k _ _, fun t k => photon_smul k t _ _⟩
def pureM (t : Tags m n) (p : Mom n) : CLinear (m:=m) (n:=n) :=
    MultilinearMap.compLinearMap (MultilinearMap.mkPiAlgebra ℂ _ _) fun i => testFunctional (t i) (p i)
lemma pure_applies (t : Tags m n) (p g) : pureM t p g = pureTest g t p := rfl

def mEarlier (x : Ambient m) (n : ℕ) : CLinear (m:=m) (n:=n) := MultilinearMap.mk' (fun g => earlier g x)
    (by
      intro h i y z
      unfold earlier; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t ht
      simp_rw [← integral_add (product_int (wave_lp x ⟨n,t⟩) (pure_lp (update h i y) _))
         (product_int (wave_lp x ⟨n,t⟩) (pure_lp (update h i z) _)), ← pure_applies, MultilinearMap.map_update_add,mul_add])
    (by
      intro h i c y; unfold earlier; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro t ht
      rw [← integral_smul]; simp only [← pure_applies,MultilinearMap.map_update_smul,mul_smul_comm])

def barList (x : TestList m) : TestList m := fun i => Probe.bar (x i)
lemma bar_update (g : Fin n → TestList m) (a : Fin n) (x : TestList m) :
    barList ∘ update g a x = update (barList ∘ g) a (barList x) := by
    funext i; by_cases h : i=a <;> simp [h]
lemma bar_smul (x : TestList m) (t : ℂ) : barList (t • x)=star t • barList x := by funext i; simp [barList]
lemma bar_add (x y : TestList m) : barList (x+y)=barList x+barList y := by funext i; simp [barList]
lemma bar_twice (x : TestList m) : barList (barList x)=x := by funext i; simp [barList]

def mConj (x : Ambient m) (n : ℕ) : CLinear (m:=m) (n:=n) :=
    MultilinearMap.mk' (fun g => star (mEarlier x n (barList ∘ g)))
      (by intro g a x y; simp only [bar_update,bar_add,MultilinearMap.map_update_add,star_add])
      (by intro g a t x; simp only [bar_update,bar_smul,MultilinearMap.map_update_smul,smul_eq_mul,star_mul,star_star]; ring)

lemma permutes (r : Equiv.Perm (Fin n)) (p : Mom n) : MeasurableEquiv.piCongrLeft (fun _=>Space3) r.symm p=p ∘ r := by
    funext i
    change (Equiv.piCongrLeft (fun _=>Space3) r.symm p i) = _; rw [Equiv.piCongrLeft_apply_eq_cast]; simp
lemma first_sym (x : Ambient m) (h : PhysicalWave x) (g : Fin n → TestList m) (r : Equiv.Perm (Fin n)) :
    earlier (g ∘ r) x = earlier g x := by
    unfold earlier
    let p : Equiv.Perm (Tags m n) := {
        toFun := fun v => v ∘ r
        invFun := fun v => v ∘ r.symm
        left_inv := fun v => by funext i; simp
        right_inv := fun v => by funext i; simp }
    rw [← Equiv.sum_comp p]
    apply Finset.sum_congr rfl; intro t ht
    let e := MeasurableEquiv.piCongrLeft (fun _=>Space3) r.symm
    have hv : MeasurePreserving e (photons n) (photons n) := measurePreserving_piCongrLeft (fun _=>photon) r.symm
    rw [← hv.integral_comp e.measurableEmbedding]
    apply integral_congr_ae; filter_upwards [h.symmetric n t r] with a ha
    change star (x (insertP ⟨n,t ∘ r⟩ (e a)))*_=_; unfold e; rw [permutes,ha];
    congr 1; exact Equiv.prod_comp r (fun i => testPhoton (g i) (t i) (a i))

def localized (m : ℕ) (f : Test4) : Submodule ℂ (TestList m) where
    carrier := {g | ∀ i, HasCompactSupport ⇑(g i) ∧ Fields.causal f (g i)}
    zero_mem' i := ⟨by change IsCompact (tsupport (0:E4→ℂ)); simp,by
        intro x hx y hy; change y∈ tsupport (0:E4→ℂ) at hy; simp at hy⟩
    add_mem' := by
        intro g h hg hh i; refine ⟨HasCompactSupport.add (hg i).1 (hh i).1,?_⟩
        intro x hx y hy; rcases tsupport_add (g i) (h i) hy with hw|hw
        · exact (hg i).2 x hx y hw
        exact (hh i).2 x hx y hw
    smul_mem' := by
        intro t g hg i; refine ⟨(hg i).1.smul_left,fun x hx y hy => (hg i).2 x hx y ?_⟩
        exact tsupport_smul_subset_right (fun _ => t) (g i) hy

def external (m : ℕ) (f : Test4) : Submodule ℝ (TestList m) where
    carrier := {g | g∈localized m f ∧ barList g=g}
    zero_mem' := ⟨(localized m f).zero_mem,by unfold barList; ext; simp⟩
    add_mem' := fun {a b} ha hb => ⟨(localized m f).add_mem ha.1 hb.1,by rw [bar_add,ha.2,hb.2]⟩
    smul_mem' := fun s x hx => by
        rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact ⟨(localized m f).smul_mem _ hx.1, by rw [bar_smul,hx.2]; congr 2; apply Complex.conj_ofReal⟩

lemma bar_localized {f : Test4} (x : TestList m) (h : x∈localized m f) : barList x∈localized m f := by
    intro i
    have he : tsupport (⇑(barList x i)) = tsupport (x i) := by
        unfold tsupport; congr 1; ext; simp [barList]
    refine ⟨(show IsCompact _ from he.symm ▸ (show IsCompact (tsupport (x i)) from (h i).1)),?_⟩
    intro a ha b hb; exact (h i).2 a ha b (he ▸ hb)
lemma accepts (m : ℕ) (f : Test4) : localized m f ≤ Submodule.span ℂ (external m f:Set (TestList m)) := by
    intro x hx
    let u := barList x; let b := I • x; let c := barList b
    have hp : x+u∈external m f := ⟨(localized m f).add_mem hx (bar_localized x hx),by rw [bar_add,bar_twice,add_comm]⟩
    have he : b+c∈external m f := ⟨(localized m f).add_mem ((localized m f).smul_mem _ hx) (bar_localized b ((localized m f).smul_mem _ hx)),by rw [bar_add,bar_twice,add_comm]⟩
    have hr : (2:ℂ)⁻¹ • (x+u)+(-I/2) • (b+c) ∈ Submodule.span ℂ (external m f:Set (TestList m)) := (Submodule.add_mem _ ((Submodule.span ℂ (external m f:Set (TestList m))).smul_mem (2:ℂ)⁻¹ (Submodule.subset_span hp)) ((Submodule.span ℂ (external m f:Set (TestList m))).smul_mem (-I/2) (Submodule.subset_span he)))
    suffices h : (2:ℂ)⁻¹ • (x+u)+(-I/2) • (b+c) = x by rwa [h] at hr
    unfold c b u; rw [bar_smul,Complex.star_def,conj_I]; funext i; ext1 j
    simp only [Pi.add_apply,Pi.smul_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul]; ring_nf; simp; ring

private lemma polar_span {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Set V) (f : MultilinearMap ℂ (fun _ : Fin n => V) ℂ)
    (h : ∀ x, (∀ i,x i∈L) → f x=0) (x : Fin n→ V) (hp : ∀ i, x i∈Submodule.span ℂ L) : f x=0 := by
    induction n with
    | zero => exact h x fun i => i.elim0
    | succ n ih =>
      rw [← Fin.cons_self_tail x]
      have he (v : V) (hv:v∈L) : f.curryLeft v (Fin.tail x)=0 :=
        ih (f.curryLeft v) (fun w hw => h (Fin.cons (α:=fun _ : Fin (n+1)=>V) v w) (fun i => Fin.cases (by simpa) (fun j=> by simpa using hw j) i)) _ (fun i => hp i.succ)
      let A : V →ₗ[ℂ] ℂ := {
                              toFun := fun y => f.curryLeft y (Fin.tail x)
                              map_add' := fun a b => by simp only [map_add, _root_.add_apply]
                              map_smul' := fun a b => by simp only [map_smul,RingHom.id_apply,_root_.smul_apply] }
      exact (Submodule.span_le.mpr (show L ⊆ LinearMap.ker A from fun v hv => he v hv)) (hp 0)

set_option maxHeartbeats 600000 in
lemma sectors_local (f : Test4) (x y : Ambient m) (p : PhysicalWave x) (q : PhysicalWave y) (h : OnVac f x y)
    (g : Fin n→ TestList m) (hc : ∀ i,g i ∈ localized m f) :
    star (earlier (barList ∘ g) x) = earlier g y := by
    let B : CLinear (m:=m) (n:=n) := mConj x n-mEarlier y n
    let L := external m f
    let D := (B.restrictScalars ℝ).compLinearMap (fun _ : Fin n=> L.subtype)
    have ht (u : Fin n → L) : D u=0 := by
        refine polar_identity D ?_ ?_ u
        · intro v r; let w i := (v i).val; change star (earlier ((barList ∘ w) ∘ r) x)-earlier (w ∘ r) y= star (earlier (barList ∘ w) x)-earlier w y; rw [first_sym x p,first_sym y q]
        intro v; let w:=v.val
        have hv : w ∈ localized m f ∧ barList w=w := v.property
        change star (earlier (fun _ : Fin n => barList w) x)-earlier (fun _ : Fin n => w) y=0
        rw [hv.2, sectors f x y h w (fun i => (hv.1 i).1) (fun i => congr_fun hv.2 i) (fun i => (hv.1 i).2) n,sub_self]
    exact sub_eq_zero.mp (polar_span L B (fun x h => ht (fun i => ⟨x i,h i⟩)) g (fun i => accepts m f (hc i)))
end YM.TraceExtension.Photons
