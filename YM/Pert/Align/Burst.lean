import YM.Pert.Align.Atom
/-! Joint line sums by character translation and reversal. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Align
open Lattice Filter Topology Full Function Atom
open scoped BigOperators Classical

variable {j k : ℕ} {G : Gauge} {n : Side}
abbrev weight (h : ℝ) (D : List Axis) : ℝ := h^(-((D.length:ℤ)+2))
def double (a : Atom j) (b : Atom k) (f : Bool) (K : Site n → ℝ) (z : Site n) := ∑ t:Kind j, ∑ s:Kind k,
    (a.degree t * b.degree s)*K (z+wrap n (a.offset t)+wrap n (coverMul f (b.offset s)))
def unroll (a : Atom j) (b : Atom k) := ∑ t:Kind j, ∑ s : Kind k,
    (a.degree t * b.degree s) * Cellular.coverLine (a.offset t - b.offset s)
lemma char_charge (a : Atom j) (b : Atom k) (z : Site n) (f : Bool) (p : Site n) :
  (∑ t : Kind j,∑ s:Kind k, (((a.degree t*b.degree s : ℝ):ℂ)*char p (z+wrap n (a.offset t)+wrap n (coverMul f (b.offset s))))) =
  ((a.factor * b.orientation f : ℝ) : ℂ) * (char p (z+wrap n (a.foot true+b.foot f)) * Band.claw (a.dirs++b.dirs) p) := by
  have he:= a.phaseA p true
  simp only [coverMul, if_true, orientation] at he
  have h (t : Kind j) (s : Kind k) := congrArg (_root_.id (α:=ℂ)) (char_add p (z+wrap n (a.offset t)) (wrap n (coverMul f (b.offset s))))
  have e : ∀ (t : Kind j) (s : Kind k), (((a.degree t*b.degree s : ℝ):ℂ)*char p (z+wrap n (a.offset t)+wrap n (coverMul f (b.offset s)))) = (char p z) * ((↑(a.degree t):ℂ) * char p (wrap n (a.offset t))) * ((b.degree s : ℂ)*char p (wrap n (coverMul f (b.offset s)))) := by
    simp only [char_add, Complex.ofReal_mul]; intro t s;ring
  let ha := ∑ i : Kind j, (↑(a.degree i):ℂ) * char p (wrap n (a.offset i))
  calc _ = (char p z * ha) * ∑ s : Kind k, (↑(b.degree s):ℂ) * char p (wrap n (coverMul f (b.offset s))) := by simp_rw [ha, Finset.mul_sum, Finset.sum_mul,e]; apply Finset.sum_comm
       _ = _ := by unfold ha; rw [he,phaseA, map_add, char_add p, char_add p]; simp only [Band.claw,List.map_append,List.prod_append,Complex.ofReal_mul];ring

lemma double_eq (a : Atom j) (b : Atom k) (h : ℝ) (z : Site n) (f : Bool) :
    weight h (a.dirs++b.dirs) * double a b f (fun s=>(toroid s).re) z = (a.factor * b.orientation f) * (Band.joint h (a.dirs++b.dirs) (z+wrap n (a.foot true+b.foot f))).re := by
  let T (t:Kind j) (s:Kind k) (p:Site n) : ℂ := ((weight h (a.dirs++b.dirs)) * (a.degree t*b.degree s):ℝ) * (topWeight n p * char p (z+wrap n (a.offset t)+wrap n (coverMul f (b.offset s))))
  have e : ((∑ t,∑ s,∑ p,T t s p):ℂ) = (∑ p, ∑ t,∑ s,T t s p) := by
    nth_rw 1 [Finset.sum_congr (s₂:=Finset.univ) rfl (f:=fun t=>∑ s,∑ p,T t s p) (g:=fun t=>∑ p, ∑ s,T t s p) (fun (t : Kind j) _ => Finset.sum_comm)]
    apply Finset.sum_comm
  calc _ = Complex.reCLM ((∑ t, ∑ s, ∑ p,T t s p):ℂ) := by
          unfold double T toroid; simp_rw [← Complex.reCLM_apply, map_sum, Finset.mul_sum, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,zero_mul, sub_zero]
          apply Finset.sum_congr rfl; intro t _; apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro p _; ring
       _ = _ := by
          let Q (p : Site n) := (((h:ℂ)^(-((((a.dirs++b.dirs).length:ℕ):ℤ)+2))) * char p (z+wrap n (a.foot true + b.foot f)) * (topWeight n p * Band.claw (a.dirs++b.dirs) p))
          have rule (p : Site n) : ((∑ t, ∑ s, T t s p):ℂ) = ((a.factor * b.orientation f : ℝ):ℂ)* Q p := by
            have he := char_charge a b z f p
            unfold T Q; simp only [Complex.ofReal_mul] at he ⊢
            calc _ = ((weight h (a.dirs++b.dirs):ℂ) * topWeight n p) * ∑ t : Kind j, ∑ s : Kind k, ((a.degree t:ℂ) * (b.degree s:ℂ) * char p (z+wrap n (a.offset t)+wrap n (coverMul f (b.offset s)))) := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl fun t _=> Finset.sum_congr rfl fun s _=>?_ ; ring
                 _ = _ := by rw [he]; unfold weight; push_cast;ring
          rw [e]; simp_rw [rule]; simp only [Complex.reCLM_apply,Band.joint,←Complex.ofReal_zpow]
          simp only [← Complex.reCLM_apply]; rw [map_sum]; simp_rw [Finset.mul_sum,← Complex.real_smul,map_smul]; simp only [Complex.reCLM_apply]
          dsimp only [Q, smul_eq_mul]; simp only [mul_assoc, ← Finset.mul_sum]
          congr 2
          rw [← Complex.reCLM_apply, map_sum];apply Finset.sum_congr rfl;intro i _
          rw [Complex.reCLM_apply,Complex.real_smul,Complex.ofReal_zpow]

structure Itinerary where
  period : ℕ → Side
  grid : ℕ → Side
  gap : ℕ→ℝ
  grid_eq (m) : (grid m).val = ((period m).val:ℝ) * gap m
  clears : Tendsto (fun u : ℕ => (grid u).val) atTop atTop
  positive (m) : 0<gap m
  cutoff : Tendsto gap atTop (𝓝 0)
  huge : ∀ d : ℕ, Tendsto (fun u:ℕ=>((period u).val:ℝ)*(gap u)^d) atTop atTop
  even_at (m) : Even ((period m).val)

abbrev StepPath (T : Itinerary) := ∀ i : ℕ, Site (T.period i)
def Scene (T : Itinerary) (x y : StepPath T) (z : E4) : Prop :=
   ∀ (p : Cover), Tendsto (fun i:ℕ=>Full.incVec (T.gap i) (Lattice.lift (x i - y i + Lattice.wrap _ p))) atTop (𝓝 z)
def Finale (T : Itinerary) (x y : StepPath T) (z : E4) : Prop := ∀ (p : Cover),
    Tendsto (fun i:ℕ=>‖Full.incVec (T.gap i) (Lattice.lift (x i + y i + Lattice.wrap _ p))‖) atTop atTop
lemma ordinary_burst (a : Atom j) (b : Atom k) (T : Itinerary) (x y : StepPath T) (z : E4) (hz : z≠0) (subT : Scene T x y z) :
    Tendsto (fun m=>weight (T.gap m) (a.dirs++b.dirs) * double a b false (fun s=> (toroid s).re) (x m-y m)) atTop (𝓝 (a.factor*b.orientation false * (Band.casual (a.dirs++b.dirs) z).re)) := by
  simp_rw [double_eq]
  let t := fun m=> x m-y m+wrap _ (a.foot true+b.foot false)
  exact Tendsto.const_mul _ ((Complex.reCLM.continuous.continuousAt (x:=Band.casual _ z)).tendsto.comp (Band.joint_casual _ _ _ _ t hz T.grid_eq T.positive T.clears T.cutoff (subT _)))
lemma final_burst (a : Atom j) (b : Atom k) (T : Itinerary) (x y : StepPath T) (z) (subT : Finale T x y z) (p : Cover) :
    Tendsto (fun m=>weight (T.gap m) (a.dirs++b.dirs)* double a b true (fun s=>(toroid s).re) (x m+y m+wrap _ p)) atTop (𝓝 (0:ℝ)) := by
  simp_rw [double_eq]
  let t := fun m=>x m+y m+wrap _ p+wrap _ (a.foot true+b.foot true)
  have ho := subT (p + a.foot true + b.foot true)
  have hp : Tendsto (fun m=>‖Full.incVec (T.gap m) (Lattice.lift (t m))‖) atTop atTop := ho.congr (fun m:ℕ => congrArg (fun x:Site (T.period m)=>‖Full.incVec (T.gap m) (Lattice.lift x)‖) (by unfold t; simp only [map_add]; abel))
  let F m := Band.joint (T.gap m) (a.dirs++b.dirs) (t m)
  have hv := Tendsto.const_mul (a.factor*b.orientation true) ((Complex.reCLM.continuous.continuousAt (x:=(0:ℂ))).tendsto.comp (show Tendsto F atTop (𝓝 0) from Band.joint_far T.period _ _ _ t T.grid_eq T.positive T.clears T.cutoff hp))
  change Tendsto (fun m=> (a.factor*b.orientation true) * (F m).re) atTop (𝓝 0)
  have hv' : Tendsto (fun m=> (a.factor*b.orientation true) * (F m).re) atTop (𝓝 ((a.factor*b.orientation true)*0)) := hv
  rw [mul_zero] at hv'; exact hv'
lemma self_burst (a : Atom j) (b : Atom k) (T : Itinerary) :
    Tendsto (fun m=> weight (T.gap m) (a.dirs++b.dirs) * (double a b false (fun s=> (toroid s).re) (0:Site (T.period m)) - unroll a b)) atTop (𝓝 (0:ℝ)) := by
  let F (m : ℕ) (t : Kind j) (s : Kind k) := (a.degree t * b.degree s) * (((toroid (wrap (T.period m) (a.offset t-b.offset s))).re - Cellular.coverLine (a.offset t-b.offset s)) * weight (T.gap m) (a.dirs++b.dirs))
  have he (t : Kind j) (s : Kind k) : Tendsto (fun m => F m t s) atTop (𝓝 0) := by
    convert! Tendsto.const_mul (a.degree t*b.degree s) (Cellular.strike_two T.period T.gap T.positive T.even_at T.huge T.cutoff ((a.dirs++b.dirs).length+2) (a.offset t-b.offset s)) using 1; simp
  simpa only [Finset.sum_const_zero] using (tendsto_finset_sum Finset.univ fun t (_: t∈Finset.univ)=> tendsto_finset_sum Finset.univ fun s (_: s∈Finset.univ)=> he t s) |>.congr (fun m=>by unfold double unroll; simp only [← Finset.sum_sub_distrib,mul_sub, Finset.mul_sum]; apply Finset.sum_congr rfl;intro t _;apply Finset.sum_congr rfl;intro s _; unfold F coverMul; rw [if_neg (by decide),zero_add,←map_add,←sub_eq_add_neg];ring)
end YM.Pert.Align
