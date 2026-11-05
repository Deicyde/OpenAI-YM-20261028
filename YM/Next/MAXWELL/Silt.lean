import YM.Next.MAXWELL.Faint

/-! # Collision expansion with isolated harmonic part -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {r s j l n : ℕ}

abbrev Scatter := E4 → ℂ

structure Silt (r : ℕ) (K : Scatter) : Prop where
  rays (t : ℝ) (h : t>0) (x : E4) : x∈away → K (t • x)=(t⁻¹^r) • K x
  pay : Clears (r-2) K

def Echoes (r : ℕ) (F K : Scatter) := ∀ x∈away, Tendsto (fun t : ℝ => (t^r) • F (t • x)) little (𝓝 (K x))

def locallyEq (K F : Scatter) := ∀ x∈away,∀ᶠ t : ℝ in little,K (t • x)=F (t • x)

/-- Up to M-1 powers below zero. Off the cone, pole versus partially cleared
product poles. -/
structure Deep (r M : ℕ) (F K : Scatter) : Prop where
  pole : Pole r K
  silts : ∃ W : ℕ → Scatter,(∀ j,Silt j (W j)) ∧ Echoes r (F-∑ j ∈ Finset.range M, W j) K

section tools
variable {f g h k : Scatter}

lemma Echoes.congr (H : Echoes r f h) (he : locallyEq f g) (hp : EqOn h k away) : Echoes r g k := by
  intro x hx; rw [← hp hx]; refine (H x hx).congr' ?_
  filter_upwards [he x hx] with t ht
  rw [ht]
lemma Echoes.less (H : Echoes r f h) (ht : r<s) : Echoes s f 0 := by
  intro x hx
  obtain ⟨w,hw⟩ := Nat.exists_eq_add_of_le ht.le
  have he : w ≠ 0 := by omega
  have hp : Tendsto id little (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs := (hp.pow w).smul (H x hx)
  rw [zero_pow he,zero_smul] at hs
  rw [add_comm] at hw
  simpa only [hw,pow_add,Pi.zero_apply,id_eq,smul_smul] using hs
lemma Echoes.add (H : Echoes r f h) (V : Echoes r g k) : Echoes r (f+g) (h+k) := by
  intro x hx; simp only [Pi.add_apply,smul_add]; exact (H x hx).add (V x hx)
lemma Echoes.neg (H : Echoes r f h) : Echoes r (-f) (-h) := by intro x hx; simp only [Pi.neg_apply,smul_neg]; exact (H x hx).neg
lemma Echoes.regular (H : ContinuousAt f 0) : Echoes 0 f (fun _ => f 0) := by
  intro x hx; have he : Tendsto (fun t : ℝ => t • x) little (𝓝 0) := by
    simpa only [zero_smul,id_eq] using! ((show Tendsto id little (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).smul_const x)
  simp only [pow_zero,one_smul]; exact H.tendsto.comp he
lemma Echoes.mul (H : Echoes r f h) (V : Echoes s g k) : Echoes (r+s) (f*g) (h*k) := by
  intro x hx; simp only [pow_add,Pi.mul_apply,mul_smul]
  have hv := (H x hx).mul (V x hx)
  refine hv.congr' (Eventually.of_forall fun y => ?_)
  rw [smul_mul_assoc, mul_smul_comm]

lemma Silt.add (H : Silt r f) (V : Silt r g) : Silt r (f+g) where
  pay := by obtain ⟨A,h,hv⟩ := H.pay; obtain ⟨B,k,hr⟩ := V.pay; exact ⟨A+B,h.add k,fun x hx => by simp only [Pi.add_apply, smul_add,hv x hx,hr x hx]⟩
  rays t ht x hx := by rw [Pi.add_apply,Pi.add_apply,H.rays _ ht _ hx, V.rays _ ht _ hx,smul_add]
lemma Silt.zero (r : ℕ) : Silt r 0 := by refine ⟨?_,0,contDiff_const,?_⟩ <;> simp
lemma Silt.twice (H : Pole r f) (V : Pole s g) (hr : 1≤r) (hv : 1 ≤ s) : Silt (r+s) (f*g) where
  pay := by
    obtain ⟨A,h,hq⟩ := H.precise; obtain ⟨B,k,hw⟩ := V.precise
    refine ⟨A*B,h.mul k,fun x hx => ?_⟩
    rw [show r+s-2=r-1+(s-1) by omega,rad_add, Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,← hq x hx,← hw x hx,smul_mul_assoc,mul_smul_comm, smul_smul]
  rays t ht x hx := by rw [Pi.mul_apply,Pi.mul_apply,H.degree t ht x hx,V.degree t ht x hx, pow_add,smul_mul_assoc,mul_smul_comm,smul_smul]
lemma ray_little (d : ℕ) {f : Scatter} (h : ∀ t : ℝ,0<t→∀ x∈away,f (t • x)=(t⁻¹^d) • f x) : Echoes d f f := by
  intro x hx; apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht; have hl : 0<t := ht
  rw [h t hl x hx,inv_pow,smul_inv_smul₀ (by positivity : t^d ≠ 0)]

private lemma sum_peel (M : ℕ) (W : ℕ → Scatter) (he : ∀ j,Silt j (W j)) {k : Scatter}
    (V : Echoes r (∑ j ∈ Finset.range M,W j) k) : Clears (r-2) k := by
  suffices hi : ∃ f : Scatter, EqOn k f away ∧ Silt r f by
    obtain ⟨f,h,A,Q,hQ,H⟩ := hi
    exact ⟨Q,hQ,fun x hx => by rw [h hx]; exact H x hx⟩
  induction M with
  | zero =>
    refine ⟨0,fun x hx => tendsto_nhds_unique (V x hx) ?_,Silt.zero r⟩
    simp
  | succ M ih =>
    have hs : Echoes M (∑ i ∈ Finset.range (M+1),W i) (W M) := by
      let A := Finset.range M
      have ht i (h : i∈ A) : Echoes M (W i) 0 := Echoes.less (ray_little i (he i).rays) (Finset.mem_range.mp h)
      have hp : Echoes M (∑ i∈A,W i) 0 := by
        intro x hx
        have hh := tendsto_finsetSum A (fun i hi => ht i hi x hx)
        simp only [Pi.zero_apply,Finset.sum_const_zero] at hh
        simp only [Finset.sum_apply,Finset.smul_sum,Pi.zero_apply]; exact hh
      rw [Finset.sum_range_succ]; simpa using Echoes.add hp (ray_little M (he M).rays)
    rcases lt_trichotomy M r with h|h|h
    · exact ⟨0,fun x hx => tendsto_nhds_unique (V x hx) (Echoes.less hs h x hx),Silt.zero r⟩
    · subst r; exact ⟨W M,fun x hx => tendsto_nhds_unique (V x hx) (hs x hx),he M⟩
    have hg : EqOn (W M) 0 away := fun x hx => tendsto_nhds_unique (hs x hx) (Echoes.less V h x hx)
    apply ih (Echoes.congr V ?_ fun i _ => rfl)
    intro x hx; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    rw [Finset.sum_range_succ,Pi.add_apply,hg (show t • x∈away from smul_ne_zero (show t>0 from ht).ne' hx),Pi.zero_apply,add_zero]

lemma Deep.clear (H : Deep r s f h) (hv : locallyEq f 0) (hr : 2 ≤ r) : EqOn h 0 away := by
  obtain ⟨W,he,hh⟩ := H.silts
  have hs : Clears (r-2) (-h) := by
    apply sum_peel s W he (Echoes.congr (Echoes.neg hh) ?_ fun _ _ => rfl)
    intro x hx; filter_upwards [hv x hx] with t ht; simp only [Pi.neg_apply,Pi.sub_apply,ht, Pi.zero_apply, zero_sub,neg_neg]
  apply clears_faint H.pole hr
  obtain ⟨A,hA,ht⟩ := hs
  refine ⟨-A,hA.neg,fun x hx => ?_⟩
  have hm := ht x hx; simp only [Pi.neg_apply,smul_neg] at hm; rw [Pi.neg_apply,← hm,neg_neg]
lemma Deep.add (H : Deep r s f h) (V : Deep r s g k) : Deep r s (f+g) (h+k) where
  pole := H.pole.add V.pole
  silts := by
    obtain ⟨W,he,H⟩ := H.silts; obtain ⟨U,hU,V⟩ := V.silts
    refine ⟨(fun j => W j+U j),fun j => Silt.add (he j) (hU j),?_⟩
    rw [Finset.sum_add_distrib, add_sub_add_comm]; exact Echoes.add H V
lemma Deep.congr (H : Deep r s f h) (he : locallyEq f g) (hp : EqOn h k away) : Deep r s g k where
  pole := H.pole.congr hp
  silts := by
    obtain ⟨W,hw,h⟩ := H.silts
    refine ⟨W,hw,Echoes.congr h (fun x hx => ?_) hp⟩
    filter_upwards [he x hx] with t ht; rw [Pi.sub_apply,ht,Pi.sub_apply]
lemma Deep.bare (H : Echoes r f h) (hp : Pole r h) : Deep r s f h where
  pole := hp
  silts := ⟨fun j => 0,Silt.zero,by simpa using H⟩
lemma Deep.carried (H : Silt r f) (hr : r<s) (l : ℕ) : Deep l s f 0 where
  pole := Pole.zero _
  silts := by
    let W (i : ℕ) := if i=r then f else 0
    refine ⟨W,fun i => ?_,?_⟩
    · by_cases h : i=r
      · subst i; rw [show W _=f from if_pos rfl]; exact H
      rw [show W _=0 from if_neg h]; exact Silt.zero i
    simp only [W,Finset.sum_ite_eq',Finset.mem_range,hr,↓reduceIte,sub_self]; intro x hx; simp
lemma Deep.zero (r s : ℕ) : Deep r s 0 0 := Deep.bare (ray_little r (Silt.zero _).rays) (Pole.zero _)
lemma Deep.sum {ι : Type*} (v : Finset ι) (f g : ι→ Scatter) (H : ∀ i ∈ v, Deep r s (f i) (g i)) :
    Deep r s (fun x => ∑ i ∈ v, f i x) (fun x => ∑ i∈v,g i x) := by
  classical
  induction v using Finset.induction_on with
  | empty => simpa using! Deep.zero r s
  | @insert i v hi ih => simp_rw [Finset.sum_insert hi]; exact Deep.add (H i (Finset.mem_insert_self ..)) (ih fun j hj => H j (Finset.mem_insert_of_mem hj))
end tools
end YM.Maxwell.Free
