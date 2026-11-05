import YM.Next.RANK.Brigade

/-!
# Pre-C,L numeric capacity: no implicit consumption of frames or calibrations

Purse planner. For fixed G, choose shape requests by d NOT Y family. Conditional
on estimates eventually achieving the post-L constants being assigned. Separately
choose e.g. toll.Foil large as a function only of pre-L credits and these orders.
`R?` post-L expenses, horizon, heat-log growth etc must still abide. No contradictory
stipend.Imports like needing a uniform Leg.life THEN fixing ratios pre-L to pay a
rate varying with mesh. If using this path, yes this WGrowth pre estimator is a
TRUE requirement not a posterior growth. Need verify when doing actual physics.

Here build before-L cost and after-L waits for the *arithmetic* part of our
estimates through `Regiment` & `ReadyRack`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Spindle Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset RG.Supply Ship Bid Labels
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G}

private lemma factor_cnt (d : ℕ) (F : Frame G d) : (∀ i : F.Index,(F.grades i).2 ≤ d) := by
  intro i; let V:=F.basis i
  have hi : V.val ≠ 0 := fun h=> F.basis.ne_zero i (Subtype.ext h)
  obtain ⟨p,hp⟩:= Finset.nonempty_iff_ne_empty.2 (show V.val.support ≠ ∅ from fun he => hi ((MvPolynomial.support_eq_empty).1 he))
  have he : Finsupp.weight bidegree p = F.grades i:= (pure_grade (F.grades i) V).1 (F.pure i) (MvPolynomial.mem_support_iff.mp hp)
  apply le_trans _ (F.bound i); rw [← he]; apply (power_le p).trans; rw [weight_slot]
lemma savings (C : Family G) (d : ℕ) : saves C d ≤ (d:ℝ)+2 := by
  have hh: Atlas.leash (C.labels.level d) ≤ d:= Finset.sup_le (fun i _ => factor_cnt d _ i)
  -- inspect nat cast in saves
  unfold saves; gcongr

/-- Pre-L and pre-C. Reserve may pad coil requests. -/
structure Panel (d : ℕ) where
  bag : ℕ→ Purse
  arc : ℝ
  huge : d+6≤arc -- enough all frames
  currency : ℝ
  θ : ℕ
  enough : d≤ θ
  factor i : (bag i).band=arc
  stable i : (bag i).taylor=θ
  loose i : arc*d+d+2≤ (bag i).credit
  vital i : (bag i).f=currency

structure Entry (S : Stage) where
  -- L1 etc pre-L projection cost floor for F clocks
  kernel : ℝ
  awake : 1 ≤ kernel
  shape : ℝ
  ceiling : 1 ≤ shape
  posts : ℕ
  age : 10 ≤ posts
  q : ℕ
  reserve : posts+10 ≤ q
  ζ : ℝ -- in practice may redeclare after L pursuant to `tabled`
  pulse : 0 < ζ
  warm : ζ ≤ S.clip.linear/20
  trunk : ℝ
  road : S.supportExponent ≤ trunk

-- independent applications can post-choose ζ smaller after Large; Digit/hike independent (details not automated)

def Panel.patronize (C : Family G) {d : ℕ} (B : Panel d) {α : ℝ} (h : 0≤ α) : Cohesion C d where
  purses:=B.bag; fixed:=B.arc;large:= by linarith only [B.huge,Nat.cast_nonneg (α:=ℝ) d]
  gain:=by linarith only [B.huge,savings C d]
  pan:=B.currency; atoms:= B.θ;numbers:=B.enough
  mark:=α; supported:= h
  sameB:= B.factor
  credit j:= by rw [B.factor]; linarith only [B.loose j, savings C d]
  funding:=B.vital
  same_size:=B.stable
private lemma pulse_price {p : Purse} {A : Stage} (h:p.budget) (he:stipend A p) (hp:p.goal+4 ≤ p.taylor) (hx:0≤p.band)
    (ht:p.horizon+10 ≤ p.era.coast.Q) (hz:10 ≤ p.horizon) :
    ∃ k : ℕ, ∀ v : Side,k≤v.val → Regiment p A v := by
  obtain ⟨k,H⟩:= eventually_atTop.mp ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (pulse_ok p hx))
  exact ⟨k+128*p.era.coast.Q,fun v hV=> ⟨h,H v (by omega),he,hp,ht,hz,by omega⟩⟩

structure Compatible {d : ℕ} (X : Panel d) (v : ℕ) {b : Stage} (S : Entry b) : Prop where
  cost : (X.bag v).era.coast.Q=S.q
  shift : (X.bag v).horizon=S.posts
  provision : (X.bag v).era.coast.a=S.ζ
  earn : (X.bag v).L=S.kernel
  book : (X.bag v).era.α=S.shape
  act : (X.bag v).era.coast.e=S.trunk
  pay : X.θ+1 ≤ b.order → ∃ k : ℕ, ∀ v' : Side, k≤v'.val → Regiment (X.bag v) b v'

lemma preSheet {P : ℕ → Stage} (d : ℕ) (S : ∀ i, Entry (P i)) (b : ℝ) (h : d+6≤b) :
    ∃ X : Panel d,X.arc=b ∧ ∀ i : ℕ, Compatible X i (S i):= by
  let credit:ℝ:= b*d+d+2; have hx:0≤ b:= by linarith only [h,Nat.cast_nonneg (α:=ℝ) d]
  have hc : 1 ≤ credit:=by unfold credit; have hp:0 ≤ b*d:=mul_nonneg hx (Nat.cast_nonneg _); linarith only [hp, Nat.cast_nonneg (α:=ℝ) d]
  let T:ℝ:= -credit-9; let U:ℝ:=1/16-T
  have he : 0 ≤ U:=by unfold U T; linarith only [hc]
  obtain ⟨n,hn⟩:= exists_nat_ge (2*U+10)
  let i:= n+d+5
  have hn' :(6:ℝ) ≤ n:= by linarith only [hn,he]
  let J:= fun x=> (⟨(S x).q,(S x).trunk,(P x).price_pos.le.trans (S x).road,U,U,he,he,(S x).ζ,(S x).pulse⟩ : Demand)
  let g:=fun x=>(⟨J x,(S x).shape,(S x).ceiling⟩:Era)
  let Φ:ℝ:= n+10*(2*credit+3+8*i+10)+10
  let p':= fun x=> (⟨g x,i,n,(S x).posts,b,credit,T,Φ,(S x).kernel,by
                        unfold Φ; linarith only [hc,hn',Nat.cast_nonneg (α:=ℝ) i],
                        (S x).awake,hc,by unfold T; linarith only,(J x).base, by exact_mod_cast hn',by linarith only [hn],by change 1/16-U=T; unfold U;ring,rfl⟩ : Purse)
  let A:Panel d:=⟨p',b,h,T,i,by unfold i;omega,fun _=>rfl,fun _=>rfl,fun _=>le_rfl,fun _=>rfl⟩
  refine ⟨A,rfl,fun x=> ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun hx'=>?_⟩⟩
  have ht:stipend (P x) (A.bag x):= ⟨le_trans (S x).road (by change _≤(S x).trunk+2;linarith only),(S x).warm,hx'⟩
  exact pulse_price (p:=p' x) (show (A.bag x).budget from le_rfl) ht (show n+4 ≤ i by unfold i; omega) hx (S x).reserve (S x).age
-- For all the quantified arities d, commit L-requests before D-basis freeze. Can encode as an enlarged
-- Sheet floor. Request on Wait afterwards (`scheduled`). Need all stages with
-- adequate order. No claim stake exponent attained at these stages.
lemma all_preSheet {X : Sheet G} (S : ∀ (_ j : ℕ), Entry (X.profile j)) (b : ℕ→ℝ) (h : ∀ d,d+6 ≤ b d) (hu : Tendsto (fun j=> (X.profile j).order) atTop atTop) :
    ∃ (P : ∀ d : ℕ, Panel d) (K : ℕ → Finset ℕ) (M : ℕ → ℕ),
      (∀ i,(P i).arc=b i ∧ ∀ᶠ j in atTop,i∈K j) ∧ ∀ j i : ℕ, i∈ K j →
        Compatible (P i) j (S i j) ∧ ∀ L : Side, M j ≤ L.val → Regiment ((P i).bag j) (X.profile j) L := by
  choose P hv ht using fun d : ℕ=> preSheet d (S d) (b d) (h d)
  let A (j) := ((range (j+1)).filter fun i=> (P i).θ+1 ≤ (X.profile j).order)
  have hp {i j} (s:i ∈ A j) := (mem_filter.mp s).2
  have hf : ∀ j i : ℕ,i∈ A j→ ∃ n : ℕ,∀ L : Side,n ≤ L.val → Regiment ((P i).bag j) (X.profile j) L:= fun j i s=> (ht i j).pay (hp s)
  choose! M hM using hf; refine ⟨P,A,(fun i=> (A i).sup (M i)), fun i => ⟨hv i,?_⟩,fun j i hj=> ⟨ht i j,fun k hk=> hM j i hj k ((le_sup hj).trans hk)⟩⟩
  filter_upwards [eventually_ge_atTop i, hu.eventually_ge_atTop ((P i).θ+1)] with j hj he
  exact mem_filter.mpr ⟨mem_range.mpr (by omega),he⟩
variable {X : Sheet G} {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}


end YM.Next.Rank.Tapes
