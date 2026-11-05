import YM.Extension.UV.Station.Fibers
import YM.Extension.UV.Station.Tight
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open RG Precision Lattice Set Function Filter
open scoped Topology BigOperators Classical
private lemma walk_roster (M:ℕ): Finite {x:Walk // x.length ≤ M} :=by
  apply Finite.of_injective (f:=fun x:{x:Walk // x.length≤M} => (⟨⟨x.1.length,Nat.lt_succ_of_le x.2⟩,List.get x.1⟩: Σ i:Fin (M+1),Fin i.1→Step))
  intro x y h; rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  have hl:=congr_arg (fun u : (Σ i:Fin (M+1),Fin i.1→Step)=> List.ofFn u.2) h
  exact Subtype.ext (by simpa using hl)
lemma slot_roster (M:ℕ): Finite {x:Slot // x.length ≤ M} :=by
  haveI:=walk_roster M
  have ho (x: {x:Slot // x.length≤M}): x.1.walk.length ≤ M:= (Nat.le_add_right ..).trans x.2
  refine Finite.of_injective (fun x: {x:Slot // x.length≤M}=> ((⟨x.1.walk,ho x⟩:{y:Walk//y.length≤M}),x.1.plaq)) fun x y h=> ?_
  obtain ⟨h₁,h₂⟩:=Prod.mk.inj h;have hh:=congr_arg Subtype.val h₁
  exact Subtype.ext (by rcases x with ⟨⟨a,b⟩,h⟩; rcases y with ⟨⟨c,d⟩,z⟩; simp only at hh h₂; cases hh; cases h₂;rfl)
lemma pattern_roster (k M) : Set.Finite {s:Pattern k|pat_len s ≤ M} := by
 haveI:=slot_roster M
 have ho (x:{x:Pattern k//pat_len x≤M})(i): (x.1 i).length ≤ M:= (Finset.single_le_sum (f:=fun i=>(x.1 i).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans x.2
 let f (x:{x:Pattern k//pat_len x≤M})(i): {s:Slot//s.length≤M} := ⟨x.1 i,ho x i⟩
 exact Finite.of_injective f (fun x y h=> Subtype.ext (by funext i; exact congr_arg Subtype.val (congr_fun h i)))

lemma sequence_extract {κ:Type*} [Countable κ] (f:ℕ→κ→ℝ) (h:∀ i,∃ c,∀ᶠ n:ℕ in atTop, |f n i| ≤ c):∃ φ:ℕ→ℕ,∃ x:κ→ℝ,StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 x):=by
   choose c hc using h; choose v hv using fun i=> eventually_atTop.mp (hc i)
   let z i:=max (1+|c i|) (∑ n∈Finset.range (v i), |f n i|)
   let B (i:κ):= _root_.Metric.closedBall (0:ℝ) (z i)
   have hb :∀ n,f n ∈Set.univ.pi B:= by
     intro n i hi; apply _root_.Metric.mem_closedBall.mpr
     rw [dist_zero_right,Real.norm_eq_abs]
     by_cases hm:n < v i
     · exact (Finset.single_le_sum (f:=fun n=>|f n i|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr hm)).trans (le_max_right ..)
     exact (hv i n (le_of_not_gt hm)).trans (le_trans (by linarith [le_abs_self (c i)]) (le_max_left ..))
   obtain ⟨a,ha,φ,hφ,hy⟩:= (isCompact_univ_pi (fun i=>isCompact_closedBall (0:ℝ) (z i)) ).tendsto_subseq (show ∀ n,f n ∈ Set.univ.pi B from hb)
   exact ⟨φ,a,hφ,hy⟩

def book_row {G:Gauge} (R:PathData G) (b:PlaqAxes)(s:Slot):ℝ := fiber (fun i=>(R.row b i).2) (fun i=>(R.row b i).1) s
lemma row_budget {G:Gauge} (R:PathData G) {u σ A L} (h:R.Bounds u σ A L) b : tight.mass (book_row R b) σ (fun s=>s.length) A:=fiber_budget (w:=fun s=>Real.exp (σ*s.length)) (fun i=>(R.row b i).2) (fun _=>Real.exp_nonneg _) (h.rows b)
lemma pat_budget {G:Gauge} (k:ℕ) (a:ℕ→Atom G k) {σ A:ℝ} (h:SumBudget (fun i=>(a i).budget σ) A) b : tight.mass (fun s=>pat_coeff a s b) σ pat_len A:= by
   refine fiber_budget (w:=fun s=>Real.exp (σ*pat_len s)) _ (fun _=>Real.exp_nonneg _) (budget_minor (fun _=> by positivity) (fun i=> ?_) h)
   unfold Atom.budget Atom.magnitude
   exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun b _=> abs_nonneg ((a i).coeff b)) (Finset.mem_univ b)) (Real.exp_nonneg (σ*(a i).length))

def book {G:Gauge} (R:PathData G) (k:Fin 3): Pattern (k.1+2) → (Fin (k.1+2)→ G.ColorIndex) → ℝ :=match k with
 | ⟨0,_⟩=>pat_coeff R.loop
 | ⟨1,_⟩=>pat_coeff R.cubic
 | ⟨2,_⟩=>pat_coeff R.quartic

def cap (k:Fin 3) (A L:ℝ):ℝ := match k with | ⟨0,_⟩=>L | ⟨1,_⟩=>A | ⟨2,_⟩=>A
lemma book_budget {G:Gauge} (R:PathData G) {p σ A L} (h:R.Bounds p σ A L) k b : tight.mass (fun s=>book R k s b) σ pat_len (cap k A L):=by
   fin_cases k <;> dsimp only [book] <;> first | exact pat_budget _ _ h.two _ | exact pat_budget _ _ h.three _ | exact pat_budget _ _ h.four _

abbrev Colors (G:Gauge) (k:Fin 3) := Fin (k.1+2)→G.ColorIndex
abbrev BookKey (G:Gauge) := (PlaqAxes × Slot) ⊕ (Σ k:Fin 3, (Colors G k) × Pattern (k.1+2))
def book_get {G:Gauge} (R:PathData G) : BookKey G → ℝ
 | Sum.inl (b,y) => book_row R b y
 | Sum.inr ⟨k,b,y⟩ => book R k y b

def book_len (G): BookKey G → ℕ
 | Sum.inl (_b,y) => y.length
 | Sum.inr ⟨_k,_b,y⟩ => pat_len y
lemma book_roster G M : Set.Finite {i |book_len G i ≤ M} := by
  let T := (PlaqAxes × {y:Slot//y.length≤M}) ⊕ (Σ k:Fin 3,(Colors G k)×{y:Pattern (k.1+2)//pat_len y≤M})
  let f (i:{i:BookKey G//book_len G i≤M}):T:= match i with | ⟨.inl (b,y),h⟩=> .inl (b,⟨y,h⟩) | ⟨.inr ⟨k,b,y⟩,h⟩=> .inr ⟨k,b,⟨y,h⟩⟩
  let h (i:T):BookKey G := match i with | .inl x=>.inl (x.1,x.2.1)| .inr ⟨k,b,y⟩=>.inr ⟨k,b,y.1⟩
  haveI hb(k:Fin 3): Fintype {y:Pattern (k.1+2)//pat_len y≤M}:= by exact @Fintype.ofFinite _ (pattern_roster (k.1+2) M).to_subtype
  letI := slot_roster M
  haveI := Fintype.ofFinite {y:Slot//y.length≤M}
  refine @Finite.of_injective _ T (show Finite ((PlaqAxes × {y:Slot//y.length≤M}) ⊕ (Σ k:Fin 3,(Colors G k)×{y:Pattern (k.1+2)//pat_len y≤M})) from inferInstance) f (fun i j hi=>?_) -- local get
  have hh (i:{y:BookKey G// book_len G y≤M}): h (f i)=i.1:=by rcases i with ⟨_ | ⟨a,b,c⟩,h⟩<;> rfl
  exact Subtype.ext ((hh i).symm.trans ((congr_arg h hi).trans (hh j)))
lemma bounded_coeff {G:Gauge} {R: ℕ→ℕ→PathData G} {p σ A L m} (h:∀ᶠ i:ℕ in atTop,(R i m).Bounds p σ A L) (y:BookKey G) : ∃ C,∀ᶠ i:ℕ in atTop,|book_get (R i m) y| ≤ C:= by
  have hb {Y:Type} {f:Y→ℝ} {C} {l':Y→ℕ} (hv:tight.mass f σ l' C) (hσ:σ≥0) x : |f x|≤ C := by
    exact (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (show 0≤ σ*l' x by positivity))).trans ((Summable.le_tsum hv.2.1 (i:=x) fun j _=> hv.1 _).trans hv.2.2)
  cases y with
  | inl z=> exact ⟨A,h.mono fun i hi=> by apply hb (f:=book_row _ _) (row_budget _ hi z.1) hi.width.le z.2⟩
  | inr z=> exact ⟨cap z.1 A L,h.mono fun i hi=> by rcases z with ⟨k,b,t⟩; exact hb (book_budget _ hi k b) hi.width.le t⟩

lemma book_extract {G:Gauge} (R: ℕ→ℕ→PathData G) (p:ℕ→Clip) (σ A L:ℕ→ℝ)
    (h:∀ m,∀ᶠ n:ℕ in atTop, (R n m).Bounds (p m) (σ m) (A m) (L m))
    (φ₀:ℕ→ℕ) (t: Tendsto φ₀ atTop atTop) : ∃ φ:ℕ→ℕ, StrictMono φ ∧ ∀ m,∃ f:BookKey G →ℝ,
      (∀ τ,τ<σ m → ∀ b, Tendsto (fun n=> tight.read (book_row (R (φ₀ (φ n)) m) b - fun s=>f (.inl (b,s))) τ (fun s=>s.length)) atTop (nhds 0)) ∧
      (∀ τ,τ<σ m → ∀ k b, Tendsto (fun n=> tight.read ((fun s=>book (R (φ₀ (φ n)) m) k s b) - (fun s=>f (.inr ⟨k,b,s⟩))) τ pat_len) atTop (nhds 0)) ∧
      Tendsto (fun n=> book_get (R (φ₀ (φ n)) m)) atTop (nhds f) := by
  obtain ⟨φ,f,hφ,hf⟩:= sequence_extract (κ:=ℕ × BookKey G) (fun i z=>book_get (R (φ₀ i) z.1) z.2) (fun i=>bounded_coeff (R:=fun n m=>R (φ₀ n) m) (t.eventually (h i.1)) i.2)
  have hf' (m): Tendsto (fun n=>book_get (R (φ₀ (φ n)) m)) atTop (nhds (fun y=>f (m,y))) :=tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mp hf (m,i)
  have hv m := hφ.tendsto_atTop.eventually (t.eventually (h m))
  refine ⟨φ,hφ,fun m=>⟨_,fun τ hτ b=>?_,fun τ hτ k b=>?_,hf' m⟩⟩
  · apply tight.strict_limit (by filter_upwards [hv m] with i hi; exact row_budget _ hi b) (tendsto_pi_nhds.mpr (fun s=> tendsto_pi_nhds.mp (hf' m) (.inl (b,s)))) (fun M=>by exact Set.finite_coe_iff.mp (slot_roster M)) hτ
  apply tight.strict_limit (by filter_upwards [hv m] with i hi; exact book_budget _ hi k b) (tendsto_pi_nhds.mpr (fun s=> tendsto_pi_nhds.mp (hf' m) (.inr ⟨_,b,s⟩))) (pattern_roster _) hτ
end YM.Extension.UV.StationaryData
