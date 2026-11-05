import YM.FullVolume.Pavilion

/-! One open ticket into the literal kernel, linear & SBP arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank.Market Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}{C:Family G} {n k N p : ℕ}

section word
variable (F : Fin n → Trial C) (i : Cutoffs)

def monitor (f : Trial C) (x : Positions (n+1)) := word (Fin.cons f F) i (wrap (C.side i.1 i.2) ∘ x)

def wing (x : Positions (n+1)) (U : Config G (C.side i.1 i.2)) := ∏ j:Fin n,F j i.1 i.2 (wrap _ (x j.succ)) U

private lemma exposed (f : Trial C) (x : Positions (n+1)) :
    monitor F i f x=moment (C.beta i.1 i.2) (fun U => f i.1 i.2 (wrap _ (x 0)) U * wing F i x U) := by
  unfold monitor word; congr 1; funext U; rw [Fin.prod_univ_succ]; simp [wing]

variable {f h: Trial C}
lemma scores_minus (hf:∀ x, Continuous (f i.1 i.2 x))(hh:∀ x, Continuous (h i.1 i.2 x))
    (hp:∀ j x, Continuous (F j i.1 i.2 x)) : monitor F i (f-h) = monitor F i f-monitor F i h:=by
  funext x; have hl:Continuous (wing F i x) := continuous_finsetProd _ (fun j _=>hp ..)
  change monitor F i (f-h) x = monitor F i f x - monitor F i h x
  rw [exposed,exposed,exposed]; unfold moment
  simp_rw [Pi.sub_apply,sub_mul]
  exact integral_sub (continuous_integrable _ ((hf _).mul hl)) (continuous_integrable _ ((hh _).mul hl))

lemma scores_scale (b : Cutoffs→ℂ) (f: Trial C):monitor F i (fun N p x=> b (N,p) • f N p x) = b i • monitor F i f := by
  funext x; rw [Pi.smul_apply,exposed,exposed]; unfold moment; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
lemma scores_change {x y: Bid.Rowe C k} (h:x i=y i) : monitor F i (Bid.upper C x)=monitor F i (Bid.upper C y):=by
  funext X; rw [exposed,exposed]; unfold Bid.upper; simp only [Prod.mk.eta,h]

lemma scores_move (hf:∀ x, Continuous (f i.1 i.2 x))(hp:∀ j x, Continuous (F j i.1 i.2 x)) (a:Axis):
    monitor F i (farther f a)=delta (tick a) (C.S.a i.1) (monitor F i f):=by
  let Q:Trial C:= fun N p o=> f N p (o+step a)
  rw [show farther f a=(fun N p o=> (C.S.a N:ℂ)⁻¹ • (Q-f) N p o) from rfl,
    scores_scale F i (fun i=> (C.S.a i.1:ℂ)⁻¹), scores_minus _ _ (fun x=> hf (x+step a)) hf hp]; ext x:1
  suffices H:monitor F i Q x=monitor F i f (x+tick a) by simp [H]
  rw [exposed,exposed]; unfold wing Q; congr 1; funext U; simp [tick,wrap_step]
lemma scores_hops (f:Trial C)(hf:∀ N p x, Continuous (f N p x))(hp:∀ j x, Continuous (F j i.1 i.2 x))(l:List Axis):
    monitor F i (hops f l) = deltas (C.S.a i.1) (l.map tick) (monitor F i f):=by
  have he (l:List Axis) : ∀ x, Continuous (hops f l i.1 i.2 x):=by
    induction l with
    | nil=> exact fun _=> hf _ _ _
    | cons a l ih=> exact fun x=> ((ih _).sub (ih x)).const_smul _
  induction l with
  | nil=>rfl
  | cons a l ih=> rw [hops,scores_move _ _ (he _) hp, ih]; rfl
end word
section witness
variable {S:Table C.book}{d : ℕ}{X:Columns C S d} (T:X.Trials) (k:ℕ) (i:Cutoffs) (j:Fin X.amount)

def wisps (u:Fin (X.row j).extra)(i:Cutoffs) := T.lift k i.1 i.2 ((X.row j).uses u)
def siblings (u:Fin (X.row j).extra):Trial C := Bid.upper C (d:=d) (wisps T k j u)

lemma ridge (x:Bid.Rowe C d)(y):
    monitor (siblings T k j) i (Bid.upper C x) y = lifted C i.1 i.2
      (fun u:Fin ((X.row j).extra+1)=> ⟨d, Fin.cons (α:=fun _=> C.label d) (x i) (fun u=> wisps T k j u i) u⟩) y:=by
  unfold monitor word; dsimp [lifted,Family.numeric]; unfold moment; apply integral_congr_ae
  refine Eventually.of_forall fun z=> Finset.prod_congr rfl (fun u _=>?_); refine Fin.cases ?_ (fun h=> ?_) u <;> rfl -- binder dependent

def liftMap (j:Fin X.amount)(i:Cutoffs) : C.label d →ₗ[ℂ] (Positions ((X.row j).extra+1)→ℂ) where
  toFun x := monitor (siblings T k j) i (Bid.upper C (fun _=>x))
  map_add' x y:= by
    let f := Bid.upper C (fun _ => x); let h:= Bid.upper C fun _=> y
    let Q := siblings T k j
    change monitor Q i _ = monitor Q i f+monitor Q i h
    have hv (w z: C.label d): Bid.upper C (fun _=>w-z)=Bid.upper C (fun _=>w)-Bid.upper C (fun _=>z):= by
      funext N p o; change C.O _ _ (d:=d) (w-z) _= C.O _ _ (d:=d) w _ - C.O _ _ (d:=d) z _
      exact ((C.linearO N p d o).mk' _).map_sub w z
    have hE : Bid.upper C (fun _=>-y) = -h:=by
      funext N p o; exact ((C.linearO N p d o).mk' _).map_neg y
    rw [show x+y=x-(-y) by abel,hv,scores_minus (f:=f) Q i (fun x=> C.continuousO ..) (fun x=>C.continuousO ..) (fun j x=> C.continuousO ..)]
    change _-(monitor Q i _) = _
    rw [hE,show -h=(fun N p o=> (-1:ℂ) • h N p o) from (by funext; simp),scores_scale _ _ (fun _=> -1)]; simp
  map_smul' x y:= by
    let f:= Bid.upper C (fun _=>y); let Q := siblings T k j
    change monitor Q i _= x • monitor Q i f
    rw [show Bid.upper C (fun _=>x • y) = (fun N p o=> x • f N p o) from ?_]; exact scores_scale _ _ (fun _=> x) _
    funext N p o; exact (C.linearO N p d o).map_smul x y

variable (b : ℝ) (l : List Axis)
def assay (f:Trial C): Fin X.amount → ℂ := fun j => blurs (steps C.S b i.1) (l.map tick) (monitor (siblings T k j) i f) (loc T k j i)

def probe : C.label d →ₗ[ℂ] (Fin X.amount → ℂ) := LinearMap.pi (fun j=> (LinearMap.proj (loc T k j i)).comp ((blurs (steps C.S b i.1) (l.map tick)).comp (liftMap T k j i)))
lemma probe_eq (x:Bid.Rowe C d) : probe T k i b l (x i) = assay T k i b l (Bid.upper C x):=by
  funext j
  change blurs _ _ (monitor _ _ (Bid.upper C (d:=d) _)) _= _; rw [scores_change (x:=fun _=> x i) (y:=x) _ _ rfl]; rfl
lemma probe_sub (x y:Trial C) (hf:∀ u, Continuous (x i.1 i.2 u))(hh:∀ u,Continuous (y i.1 i.2 u)): assay T k i b l (x-y)= assay T k i b l x-assay T k i b l y:=by
  funext j; change blurs _ _ _ _ = blurs _ _ _ _ - blurs _ _ _ _
  rw [scores_minus _ _ hf hh (fun j z=> C.continuousO ..),map_sub]; rfl
end witness
end YM.FullVolume
