import YM.Push.LOCAL_SPLITTING.Calculus

/-!
# Ordered left and right derivatives on complementary sets of oriented links

Flipping a positive link gives **right** increments (with the shifted
starting vertex and negative color direction). A successive list of flips
is not in general the ordered left derivative with directions conjugated
in that order. Prove a split & reverse formula on disjoint link sectors by
commuting a fixed left derivative through all right derivatives. No constants
from uncontrolled products of polynomial position weights at one link.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

abbrev LR (G : Gauge) (n : Side) := Directions G n × Directions G n

def mix (U : Config G n) (p : LR G n) : Config G n :=
  fun i => G.lieExp (p.1 i) * U i * G.lieExp (p.2 i)

def byLeft (a : Directions G n) : LR G n := (a,0)
def byRight (a : Directions G n) : LR G n := (0,a)
def rotateRight (U : Config G n) (a : Directions G n) : Directions G n :=
  fun l => G.adjoint (U l) (a l)

@[simp] theorem mix_zero (U : Config G n) : mix U 0 = U := by funext i; simp [mix]
theorem mix_left (U : Config G n) (a : Directions G n) (t : ℝ) : mix U (t • byLeft a) = increment U (t • a) := by
  funext i; simp [mix,byLeft,increment]
theorem mix_right (U : Config G n) (a : Directions G n) (t : ℝ) : mix U (t • byRight a) = increment U (t • rotateRight U a) := by
  funext i; apply G.mat_injective
  have he (g : G.El) (x : G.Color) :
      G.mat (G.lieExp (G.adjoint g x)) * G.mat g = G.mat g * G.mat (G.lieExp x) := by
    rw [G.mat_lieExp, G.mat_lieExp, G.mat_adjoint, G.exp_conjugate]
    simp [Gauge.conjugate,mul_assoc]
  simp only [mix,byRight,rotateRight,increment,G.mat_mul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Pi.zero_apply, smul_zero, G.mat_lieExp_zero, one_mul]
  rw [← map_smul,he]

section Smooth
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def mixJets (f : Config G n → Y) : List (LR G n) → Config G n → Y
  | [], U => f U
  | p::l, U => deriv (fun t : ℝ => mixJets f l (mix U (t • p))) 0

private theorem chart_mix {U : Config G n} {f : Config G n → Y} {k : ℕ} (hf : Chart k f U) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (f ∘ mix U) 0 :=
  chart_comp (by simpa using hf) (fun l => by
    simp only [mix, G.mat_mul]; exact (((G.exp_jet.comp ((contDiff_apply ..).comp contDiff_fst)).mul contDiff_const).mul (G.exp_jet.comp ((contDiff_apply ..).comp contDiff_snd))).contDiffAt)

private theorem mix_near {U : Config G n} {f : Config G n → Y} {k : ℕ} (hf : Chart k f U) (p : LR G n) :
    ∀ᶠ t : ℝ in 𝓝 0, Chart k f (mix U (t • p)) :=
  chart_eventually (by simpa using hf) (fun i => by
    simp only [mix, G.mat_mul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
    exact (((G.exp_jet.comp (contDiff_id.smul contDiff_const)).mul contDiff_const).mul (G.exp_jet.comp (contDiff_id.smul contDiff_const))).contDiffAt)

theorem mix_chart {U : Config G n} {f : Config G n → Y}
    (l : List (LR G n)) (k : ℕ) (hf : Chart (l.length+k) f U) : Chart k (mixJets f l) U := by
  induction l generalizing k with
  | nil => simpa! only [List.length_nil, Nat.zero_add] using hf
  | cons p l ih =>
    let V (b : Directions G n) (t : ℝ) := mixJets f l (mix (increment U b) (t • p))
    change ContDiffAt ℝ _ (fun b : Directions G n => fderiv ℝ (V b) 0 1) 0
    have he := ih (k+1) (by simpa [add_right_comm, add_assoc, add_left_comm, add_comm] using hf)
    have hQ : ContDiffAt ℝ (↑(k+1 : ℕ)) (uncurry V) 0 := by
      let W (z : Directions G n × ℝ) := mix (increment U z.1) (z.2 • p)
      exact chart_comp (k:=k+1) (x:=0) (W:=W) (by simpa only [W, Prod.fst_zero, Prod.snd_zero,zero_smul, mix_zero, Work.G07.at_zero_increment] using he) (fun i => by
        simp only [W,mix,increment,G.mat_mul, Pi.smul_apply,Prod.smul_fst,Prod.smul_snd]
        exact (((G.exp_jet.comp (contDiff_snd.smul contDiff_const)).mul
          ((G.exp_jet.comp ((contDiff_apply ..).comp contDiff_fst)).mul contDiff_const)).mul
          (G.exp_jet.comp (contDiff_snd.smul contDiff_const))).contDiffAt)
    exact (hQ.fderiv (f:=V) (g:=fun _ => 0) (m:=↑k) contDiffAt_const (by push_cast; rfl)).clm_apply (g:=fun _ => (1:ℝ)) contDiffAt_const

private theorem mix_cons {U : Config G n} {f : Config G n → Y}
    (p : LR G n) (l : List (LR G n)) (hf : Chart (l.length+1) f U) :
    mixJets f (p::l) U = fderiv ℝ (mixJets f l ∘ mix U) 0 p := by
  have ht := chart_mix (mix_chart l 1 hf)
  have hx : HasDerivAt (fun t : ℝ => t • p) p 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const p
  rw [← show (fun t : ℝ => t • p) 0 = 0 from zero_smul ..] at ht
  simpa only [mixJets,comp_def,zero_smul] using ((ht.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hx).deriv

private theorem mixed_partials {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (V : ℝ × ℝ → Y) (h : ContDiffAt ℝ 2 V 0) :
    deriv (fun t : ℝ => deriv (fun u : ℝ => V (t,u)) 0) 0 = deriv (fun u : ℝ => deriv (fun t : ℝ => V (t,u)) 0) 0 := by
  have ds (f : ℝ × ℝ → Y) (t : ℝ) (h : DifferentiableAt ℝ f (t,0)) : Analysis.D (0,1) f (t,0) = deriv (fun u => f (t,u)) 0 := by
    have he := (hasDerivAt_const (x:=(0:ℝ)) t).prodMk (hasDerivAt_id' 0)
    exact (h.hasFDerivAt.comp_hasDerivAt 0 (f:=fun u => (t,u)) he).deriv.symm
  have ds' (f : ℝ × ℝ → Y) (t : ℝ) (h : DifferentiableAt ℝ f (0,t)) : Analysis.D (1,0) f (0,t) = deriv (fun u => f (u,t)) 0 := by
    have he := (hasDerivAt_id' (0:ℝ)).prodMk (hasDerivAt_const _ t)
    exact (h.hasFDerivAt.comp_hasDerivAt 0 (f:=fun u => (u,t)) he).deriv.symm
  have H := Analysis.commuteD h (1,0) (0,1)
  have h' (a) := (Analysis.dSmooth (m:=1) h a (by norm_num)).differentiableAt one_ne_zero
  rw [show (0:ℝ × ℝ)=(0,0) from rfl, ds' _ _ (h' _), ds _ _ (h' _)] at H
  refine Eq.trans ?_ (H.trans ?_) <;> apply Filter.EventuallyEq.deriv_eq
  · filter_upwards [((continuous_id.prodMk (continuous_const (y:=(0:ℝ)))).tendsto 0).eventually (h.eventually (by simp))] with t ht
    exact (ds V t (ht.differentiableAt (by norm_num))).symm
  · filter_upwards [(((continuous_const (y:=(0:ℝ))).prodMk continuous_id).tendsto 0).eventually (h.eventually (by simp))] with t ht
    exact ds' V t (ht.differentiableAt (by norm_num))

private theorem mix_commute {C : Directions G n} {p : LR G n} {f : Config G n → Y} {U : Config G n}
    (hf : Chart 2 f U) (hC : ∀ i, C i = 0 ∨ p.1 i = 0) :
    leftDerivs (mixJets f [p]) [C] U = mixJets (leftDerivs f [C]) [p] U := by
  let Q (x : ℝ × ℝ) := mix (increment U (x.1 • C)) (x.2 • p)
  have hQ : ContDiffAt ℝ 2 (f ∘ Q) 0 := by
    have ht := chart_comp (k:=2) (x:=0) (W:=Q) (by simpa [Q,Work.G07.at_zero_increment] using hf) fun i => by
      simp only [Q, mix, increment,G.mat_mul,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd]; exact
        (((G.exp_jet.comp (contDiff_snd.smul contDiff_const)).mul ((G.exp_jet.comp (contDiff_fst.smul contDiff_const)).mul contDiff_const)).mul (G.exp_jet.comp (contDiff_snd.smul contDiff_const))).contDiffAt
    exact ht
  have he (s t : ℝ) : Q (s,t) = increment (mix U (t • p)) (s • C) := by
    funext i; obtain H|H := hC i <;> simp [Q,mix,increment,H,mul_assoc]
  change deriv (fun t : ℝ => deriv (fun u : ℝ => (f ∘ Q) (t,u)) 0) 0 = _
  rw [mixed_partials _ hQ]; simp_rw [comp_apply,he]; rfl

theorem mix_swap {C : Directions G n} {l : List (LR G n)} {f : Config G n → Y} {U : Config G n}
    (hf : Chart (l.length+1) f U) (hC : ∀ p∈l, ∀ i, C i = 0 ∨ p.1 i = 0) :
    leftDerivs (mixJets f l) [C] U = mixJets (leftDerivs f [C]) l U := by
  induction l generalizing U with
  | nil => rfl
  | cons p l ih =>
    have ht : Chart (l.length+2) f U := hf
    change leftDerivs (mixJets (mixJets f l) [p]) [C] U = _
    rw [mix_commute (mix_chart l 2 ht) (hC _ List.mem_cons_self)]
    simp only [mixJets]; apply Filter.EventuallyEq.deriv_eq
    filter_upwards [mix_near (ht.of_le (Nat.cast_le.mpr (Nat.le_succ (l.length+1)))) p] with t hv
    exact ih hv (fun a ha => hC a (List.mem_cons_of_mem _ ha))

end Smooth

section Convert
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def convertOrder (U : Config G n) : List (LR G n) → List (List (Directions G n))
  | [] => [[]]
  | p::l => ((convertOrder U l).map (fun s => p.1 :: s)) ++ ((convertOrder U l).map (fun s => s ++ [rotateRight U p.2]))

@[simp] theorem convert_length (U : Config G n) (l : List (LR G n)) :
    (convertOrder U l).length = 2^l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [convertOrder,List.length_append,List.length_map,List.length_cons,ih,pow_succ]; omega

theorem convert_mem (U : Config G n) (D : Directions G n → Prop) (l : List (LR G n))
    (h : ∀ p∈l, D p.1 ∧ D (rotateRight U p.2)) :
    ∀ s∈convertOrder U l, s.length = l.length ∧ ∀ v∈s, D v := by
  induction l with
  | nil => simp [convertOrder]
  | cons p l ih =>
    have he := ih (fun q hq => h q (by simp [hq]))
    obtain ⟨h1,h2⟩ := h p (by simp)
    intro s hs; obtain h|h := List.mem_append.mp hs <;> obtain ⟨s,hs',rfl⟩ := List.mem_map.mp h
    · simpa [h1] using he s hs'
    refine ⟨by simp [(he s hs').1],fun v hv => ?_⟩
    obtain h|h := List.mem_append.mp hv
    · exact (he s hs').2 v h
    exact (List.mem_singleton.mp h) ▸ h2

private theorem convert_edit (U : Config G n) (l : List (LR G n)) (C : Directions G n)
    (h : ∀ p∈l, ∀ i, C i = 0 ∨ p.2 i = 0) : convertOrder (increment U C) l = convertOrder U l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have ht : rotateRight (increment U C) p.2 = rotateRight U p.2 := funext fun i => by
      obtain h|h := h p (by simp) i <;> simp [rotateRight,increment,h]
    simp only [convertOrder, ht, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

private theorem list_hasDeriv {ι : Type*} (g : ι → ℝ → Y) (g' : ι → Y) (l : List ι)
    (hg : ∀ i∈l, HasDerivAt (g i) (g' i) 0) : HasDerivAt (fun t : ℝ => (l.map (fun i => g i t)).sum) (l.map g').sum 0 := by
  induction l with
  | nil => exact hasDerivAt_const _ _
  | cons i l ih => exact (hg i (by simp)).add (ih fun j hj => hg j (List.mem_cons_of_mem _ hj))

/-- Split into ordinary ordered left jets at a base point. The support
hypothesis is precisely the disjoint positive/negative sector condition
(no link belongs to both in the full list of test directions). -/
theorem mix_convert {k : ℕ} (U : Config G n) (l : List (LR G n)) (f : Config G n → Y)
    (h : ∀ p∈l, ∀ q∈l, ∀ i, p.1 i = 0 ∨ q.2 i = 0) (hf : Chart k f U) (hl : l.length ≤ k) :
    mixJets f l U = ((convertOrder U l).map (fun s => leftDerivs f s U)).sum := by
  induction l generalizing f U k with
  | nil => simp [convertOrder,mixJets,leftDerivs]
  | cons p l ih =>
    have hh : ∀ q∈l, ∀ r∈l, ∀ i, q.1 i = 0 ∨ r.2 i = 0 := fun _ ha _ hb => h _ (by simp [ha]) _ (by simp [hb])
    have he : l.length+1 ≤ k := hl
    have ht : Chart (l.length+1) f U := hf.of_le (Nat.cast_le.mpr he)
    have hsplit : mixJets f (p::l) U = mixJets f (byLeft p.1 :: l) U + mixJets f (byRight p.2 :: l) U := by
      simp only [mix_cons _ _ ht, ← map_add, show byLeft p.1 + byRight p.2 = p by ext <;> simp [byLeft,byRight]]
    rw [hsplit, convertOrder, List.map_append,List.sum_append,List.map_map,List.map_map]; apply congr_arg₂ (· + ·)
    · simp only [mixJets,mix_left]
      apply ((list_hasDeriv (fun s t => leftDerivs f s (increment U (t • p.1)))
        ((fun s => leftDerivs f s U) ∘ (p.1 :: ·)) (convertOrder U l) (fun s hs => left_has p.1
          (l:=s) (by simpa only [(convert_mem U (fun _ => True) l (by simp) s hs).1] using l.length.lt_succ_self) ht)).congr_of_eventuallyEq ?_).deriv
      filter_upwards [chart_near hf p.1] with t hv
      exact (ih _ _ hh hv (by omega)).trans (by rw [convert_edit]; exact fun q hq i => (h p (by simp) q (by simp [hq]) i).imp (fun he => by simp [he]) id)
    let C := rotateRight U p.2
    have hC (q : LR G n) (hq : q∈l) (i) : C i = 0 ∨ q.1 i = 0 := (h q (by simp [hq]) p (by simp) i).symm.imp (fun he => by simp [C, rotateRight,he]) id
    rw [show mixJets f (byRight p.2 :: l) U = leftDerivs (mixJets f l) [C] U from by simp [mixJets,leftDerivs,C,mix_right], mix_swap ht hC]
    rw [ih _ _ hh (leftDerivs_chart [C] l.length (show Chart ([C].length+l.length) f U from by simpa [Nat.add_comm] using ht)) le_rfl]
    simp [comp_def,Work.G07.left_append,C]
end Convert
end YM.Push.Local
