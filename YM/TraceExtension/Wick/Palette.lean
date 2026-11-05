import YM.TraceExtension.Wick.Refute

/-! No filtration assumptions. Include more explicit representation of
 polynomial fields' two-point kernels in momentum-test space. Each elementary
 polarized two-point kernel (for derivatives etc include derivative tags) has
 finite many mass shells and finite polynomial numerator. Comparing polynomial
 Wick fields, TWO-POINTS are given by the usual cross-vertex pairings with
 those kernels. Allow complex and even arbitrary statistics signs/coefs,
 inclusion of unit. Define the needed comparisons just by these tests; no
 Wightman postulates/construction of a massive Wick theory needed here. Tensor
 product Schwartz tests seeing compact total momentum suffice throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Wick
open Function Set Filter Asymptotics Metric Complex Mink Boundary MeasureTheory Measure
open scoped Topology BigOperators NNReal ENNReal Classical ContDiff

lemma Track.read_int (s : Track) {f : E4→ℂ} (he:Continuous f) (ht: HasCompactSupport f) : Integrable (s.tariff f) := by
    let g := fun x:E4 => Real.exp (time x) *‖f x‖
    have hc : Continuous g := by unfold g; fun_prop
    have hs : HasCompactSupport g := HasCompactSupport.mul_left (ht.comp_left (norm_zero (E:=ℂ)))
    obtain ⟨R,hR⟩ := (hs.isCompact_range hc).bddAbove
    have hp (x:E4) : ‖f x‖ ≤ R*Real.exp (-(1:ℝ)*time x) := by
       have hh : Real.exp (time x)*‖f x‖≤ R := hR (mem_range_self x)
       rw [neg_mul,one_mul,Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),mul_comm]; exact hh
    apply ((s.damped_int 1 one_pos).norm.const_mul R).mono'
    · unfold Track.tariff; apply Measurable.aestronglyMeasurable; apply Measurable.smul (f:=s.weight) _ ((he.comp s.order_cont).measurable)
      unfold Track.weight; apply Finset.measurable_prod; intro i _; unfold Mode.density freq; have hi := (s.modes i).cont; fun_prop
    filter_upwards with p
    unfold Track.tariff; rw [norm_smul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le];
    exact (mul_le_mul_of_nonneg_left (hp (s.order p)) (norm_nonneg _)).trans_eq (mul_left_comm ..)

/-- Monomial syntax suffices and makes allowed differential order explicit. -/
structure Numer where
    l : ℕ
    c : Fin l→ℂ
    d₀ : Fin l → ℕ
    d : Fin l → SpaceAxis → ℕ
namespace Numer
variable (N : Numer)

def monom (i : Fin N.l) (p:Space3) := ∏ a, p a ^ N.d i a
@[fun_prop] lemma monom_cont (i:Fin N.l) : Continuous (N.monom i) := by unfold monom; fun_prop
lemma monom_smul (i:Fin N.l)(p:Space3) (s:ℝ) : N.monom i (s•p)=s ^ (∑ a,N.d i a) * N.monom i p := by unfold monom; simp [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

def eval (p : E4) : ℂ := ∑ i, N.c i * (((time p ^N.d₀ i * N.monom i (spatial p)):ℝ):ℂ)
end Numer

structure Hue where
    mass : ℝ≥0
    num : Numer
namespace Hue
variable (h : Hue)
def forward (p : Space3) := position p (freq h.mass ‖p‖)
def value (p : Space3) : ℂ := (1/(2*freq h.mass ‖p‖):ℝ) • h.num.eval (h.forward p)
def monochrome (i : Fin h.num.l) : Mode := ⟨h.mass,∑ a,h.num.d i a,h.num.d₀ i,h.num.monom i, h.num.monom_cont _,fun p s _ => h.num.monom_smul i p s⟩
lemma forwards (i p): h.forward p=(monochrome h i).onboard p := rfl
lemma coloration (p) : value h p=∑ i, h.num.c i * ((monochrome h i).density p:ℂ) := by
    unfold value Numer.eval forward; simp only [time_position,spatial_position,Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _; change _=_*(((1/(2*freq h.mass ‖p‖):ℝ)*freq h.mass ‖p‖^ (h.num.d₀ i)*h.num.monom i p:ℝ):ℂ); rw [mul_assoc,Complex.ofReal_mul,Complex.real_smul,mul_left_comm]; rw [Complex.ofReal_mul,Complex.ofReal_mul]
end Hue

/-- Wick test, one Fourier term on every arc. Total momentum is the relative
 one (test conventions fixed elsewhere). -/
def exhibit {n:ℕ} (arcs:Fin n → Hue)(f:E4→ℂ):=∫ p:Fin n→Space3, (∏ i,(arcs i).value (p i))*f (∑ i,(arcs i).forward (p i))

/-- Includes comparison even just on compact smooth Fourier tests. -/
def Painted (a : (E4→ℂ)→ℂ) := ∃ x:Collection,∀ f:E4→ℂ, Continuous f →HasCompactSupport f→ tests x f=a f
lemma painted_tariff (x:Track) : Painted (x.read) := ⟨[(1,x)],by simp [tests]⟩
lemma painted_zero : Painted fun _ => 0 := ⟨[],by simp [tests]⟩
lemma Painted.times {a} (h:Painted a) (c:ℂ) : Painted fun v=> c*a v := by
    obtain ⟨x,hx⟩:=h; refine ⟨x.map fun i=>(c*i.1,i.2),?_⟩
    intro f he h; dsimp only; rw [← hx f he h]; clear hx; induction x with
    | nil=> simp [tests]
    | cons y z ih=> unfold tests; rw [List.map_cons,List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,mul_add, mul_assoc]; rw [tests,tests] at ih; rw [ih]
lemma Painted.andrea {a b} (h:Painted a) (hp:Painted b) : Painted fun v=> a v+b v := by
    obtain ⟨x,hx⟩:=h; obtain ⟨y,hy⟩:=hp; refine ⟨x++y,?_⟩; intro f he H; dsimp only; rw [← hx f he H,← hy f he H]; simp [tests]
lemma Painted.sum {ι:Type*} (s:Finset ι)(w:ι→(E4→ℂ)→ℂ)(h:∀ i, Painted (w i)): Painted fun v=>∑ i∈s, w i v:=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact painted_zero
    | insert i s he ih=> simp only [Finset.sum_insert he]; exact (h i).andrea ih
lemma exhibit_painted {n} (arcs:Fin n→Hue) : Painted (exhibit arcs) := by
    let V:= (i:Fin n) → Fin (arcs i).num.l; letI : Fintype V:=by unfold V; infer_instance
    let m (p:V):Track:=⟨n,fun i=>(arcs i).monochrome (p i)⟩
    let a (p:V) : ℂ :=∏ i, (arcs i).num.c (p i)
    obtain ⟨x,hx⟩:=Painted.sum Finset.univ (fun p : V=>fun v:E4→ℂ=> a p * (m p).read v) fun p=> Painted.times (painted_tariff _) _
    refine ⟨x,?_⟩; intro f he hW
    rw [hx _ he hW,exhibit]; simp_rw [Track.read,← integral_const_mul]
    have hr:=fun p:V=> ((m p).read_int he hW).const_mul (a p)
    rw [← integral_finsetSum (μ:=volume (α:= Fin n → Space3)) (f:=fun p:V => fun k=> a p*(m p).tariff f k) Finset.univ (fun p _=>hr p)];
    congr! 1; ext1 k
    simp_rw [Hue.coloration]
    rw [Fintype.prod_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro p _; unfold Track.tariff; rw [Finset.prod_mul_distrib,Complex.real_smul];
    rw [show ∑ i,(arcs i).forward (k i)=(m p).order k from rfl, mul_assoc]; unfold a Track.weight; rw [Complex.ofReal_prod]

universe u
/- Flavors include derivative tags. Arbitrary set of Wick field generators;
 finite sums as needed. Left tags can be any adjoint/dual conventions.
 Pairings may have arbitrary constant coefficients. -/
variable {Flavor: Type u}
structure MonomField (Flavor:Type u) where
    l : ℕ
    entries : Fin l → Flavor
structure Palette (Flavor:Type u) where
    span : Flavor→Flavor→ℕ
    rgb : (x y:Flavor)→ Fin (span x y)→Hue
    coefficientPair : (u v:MonomField Flavor)→(Fin u.l ≃ Fin v.l)→ℂ
namespace Palette
variable (P:Palette Flavor)
def branch (u v:MonomField Flavor) (r:Fin u.l ≃ Fin v.l) (x:E4→ℂ) : ℂ :=
    ∑ b:(i:Fin u.l)→Fin (P.span (u.entries i) (v.entries (r i))), exhibit (fun i=> P.rgb _ _ (b i)) x
lemma branch_painted (u v:MonomField Flavor) (r:Fin u.l ≃ Fin v.l) : Painted (P.branch u v r) := Painted.sum Finset.univ _ fun _=> exhibit_painted _

def pairing (u v:MonomField Flavor) (x:E4→ℂ) : ℂ := ∑ r:Fin u.l≃ Fin v.l,P.coefficientPair u v r * P.branch u v r x
lemma pairing_painted (u v: MonomField Flavor) : Painted (P.pairing u v) := Painted.sum Finset.univ _ fun _=> (P.branch_painted u v _).times _
end Palette

structure PolyField (Flavor:Type u) where
    l : ℕ
    terms : Fin l → MonomField Flavor
    amplitude : Fin l→ℂ

def Palette.wicks (P:Palette Flavor) (q w:PolyField Flavor) (v:E4→ℂ) : ℂ :=
    ∑ i:Fin q.l, ∑ j:Fin w.l, (q.amplitude i*w.amplitude j)*P.pairing (q.terms i) (w.terms j) v
lemma Palette.wicks_painted (P:Palette Flavor)(q w:PolyField Flavor) : Painted (P.wicks q w) :=
    Painted.sum Finset.univ _ fun i=> Painted.sum Finset.univ _ fun j=> (P.pairing_painted (q.terms i) (w.terms j)).times _

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {A : ℝ}
theorem wick_excludes (ht : EuclideanAsymptotic F A)(hA : 0<A) (P:Palette Flavor)(q w:PolyField Flavor) :
    ¬ ∀ f g:Probe E4, HasCompactSupport ⇑(waveTest (productTest f g)) →
       F.A.world.W 2 (pairV F.action.J (pinned F)) (productTest f g)= P.wicks q w (waveTest (productTest f g)) := by
    obtain ⟨x,hx⟩:= P.wicks_painted q w; exact fun h=> polynomial_excludes ht hA x fun f g H=> (h f g H).trans (hx _ (SchwartzMap.continuous _) H).symm
end YM.TraceExtension.Wick
#print axioms YM.TraceExtension.Wick.wick_excludes
