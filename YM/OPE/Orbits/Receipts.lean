import YM.OPE.Orbits.Rent

/-! Test of the calibrated direct error at every averaged fixed readout of
our new Reader. Constants/extraction order remain the actual construction's;
only manipulating weights and detector kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Extraction Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] measO borelO hμ

variable {G:Gauge} {C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
    {I J L:Type} [Fintype I] [Fintype J] {A:L→ℝ}{φ:Filter L}(hA:Tendsto A φ atTop) [φ.NeBot]
    {d:I→ℕ}{e:J→ℕ}{a b c:ℝ} {x:L→ I→ E4}{y:L→ J→ E4}{o:L→E4}
variable (v:Labels S d)(hx:enveloped φ A a x o)(hk:Kept φ A a x)(ha:0<a)
    {w:L→Labels S e} (hy:Kept φ A 0 y)(hp:Intervals φ A 0 (fun l=>sole (o l)) y)(hw:∀ j, RateLE φ A (fun l=>w l j) 0)

def singleError (U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(m:ℕ)
    (x:L→I→E4)(o:L→E4)(v:Labels S d)(l:L) (e:Exterior C.book)(k:Ortho):ℂ:=
      discrepancy S m (x l) (o l) v (shadowOld R.port m (x l) (o l) v) (swung e k (o l)) (turnsPort U.sector.turns k e)

def errorColor (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(m:ℕ)(x:L→I→E4)(o:L→E4)(v:Labels S d)(l:L)
    (e:Exterior C.book)(k:Ortho):ℂ:=discrepancy S m (x l) (o l) (bar U.room.kernel.spin v) (S.conj U.room.kernel.spin m (shadowOld R.port m (x l) (o l) v)) (swung e k (o l)) (turnsPort U.sector.turns k e)

include U R h hA hx hk ha hy hp hw
private lemma old_at (m:ℕ): RateLE φ A (fun l=>discrepancy S m (x l) (o l) v (shadowOld R.port m (x l) (o l) v) (y l) (w l)) ((weight d-m-1)*a) := by
     apply old_moving U hA (r:=fun _=>none) v hx hk hp hy ha (le_refl 0) ?_ w hw
     intro w; refine (discrepancy_rate_old U R h hA (fun _=>none) v w hx hk hp hy ha le_rfl ha le_rfl m).mono ?_; ring_nf; rfl

omit hy U R h hA hx hk hp hw ha
lemma whole_bar {x:I→E4}{v:Labels S d}{y:J→ E4}{w:Labels S e}(v':S.RealSpin)(h:S.Hierarchy)(hx:Injective (beside x y)) : whole S x (bar v' v) y (bar v' w)=star (whole S x v y w) :=by
     unfold whole; apply Eq.trans ?_ (bar_observes v' h (fun _=>le_rfl) (y:=beside x y) hx); apply congr_arg; funext i; cases i <;> rfl

include U R h hA hx hk ha hy hp hw
private lemma tintCost (m:ℕ) : RateLE φ A (fun l=>discrepancy S m (x l) (o l) (bar U.room.kernel.spin v) (S.conj U.room.kernel.spin m (shadowOld R.port m (x l) (o l) v)) (y l) (w l)) ((weight d-m-1)*a):=by
    have hh:∀ j:J,RateLE φ A (fun l=>(bar U.room.kernel.spin (w l)) j) 0:=fun j=>pay_fixed hA (conjugateR _ _) (hw j)
    let f l:=discrepancy S m (x l) (o l) v (shadowOld R.port m (x l) (o l) v) (y l) (bar U.room.kernel.spin (w l))
    have hd := old_at U R h hA v hx hk ha hy hp hh m; refine hd.transfer (G:=fun l=> discrepancy S m (x l) (o l) (bar U.room.kernel.spin v) (S.conj U.room.kernel.spin m (shadowOld R.port m (x l) (o l) v)) (y l) (w l)) ?_
    obtain ⟨h₁,h₂⟩:=clearance_both hA hx hk hp hy ha le_rfl; filter_upwards [h₁,h₂] with l ho hz
    refine le_of_eq (Eq.trans (b:=‖star (f l)‖) ?_ (norm_star _)); apply congr_arg norm; unfold f; rw [discrepancy,discrepancy,star_sub]; change _ - (whole S (sole _) _ (y l) (w l))=_ -(star (whole S (sole _) _ _ (bar _ (w l))))
    have hw:= whole_bar (v:=v) (w:=bar U.room.kernel.spin (w l)) U.room.kernel.spin U.room.kernel hz
    have ht:= whole_bar (v:=fun _=>shadowOld R.port m (x l) (o l) v) (w:=bar U.room.kernel.spin (w l)) U.room.kernel.spin U.room.kernel ho
    rw [bar_bar] at ht; rw [← hw,bar_bar]; exact congr_arg (_-·) (show _=_ from ht)
omit hw hy hp
section
local notation "P" => R.port
local notation "X" => U.sector.turns
local notation "ρ" => U.room.kernel.spin
variable (m n:ℕ)
private lemma spin_old (k:L→Ortho)(y:Exterior C.book)(i:Mode U.sector.derivatives): RateLE φ A (fun s=> ((R.port.sheet i) y * singleError U R m x o v s y (k s)) • U.sector.turns.act _ (k s) (R.port.loaded i n)) ((weight d-m-1)*a):=by
   obtain ⟨ht,hs⟩:= shrinking_port (o:=o) hA y k; have hc:=old_at (C:=C) U R h hA v hx hk ha ht hs (turn_port_rate hA R.law y k) m
   refine (((RateLE.const _ hA).mul hc).smul (loaded_rate hA P R.law n i k)).mono ?_; ring_nf; rfl

private lemma spin_tint (k:L→Ortho)(y:Exterior C.book)(i:Mode U.sector.derivatives): RateLE φ A (fun s=> ((R.port.sheet i) y * errorColor U R m x o v s y (k s)) • U.sector.turns.act _ (k s) (R.port.loaded i n)) ((weight d-m-1)*a):=by
   obtain ⟨ht,hs⟩:= shrinking_port (o:=o) hA y k; have hc:=tintCost U R h hA v hx hk ha ht hs (turn_port_rate hA R.law y k) m
   refine (((RateLE.const _ hA).mul hc).smul (loaded_rate hA P R.law n i k)).mono ?_; ring_nf; rfl
omit h in
lemma margins : ∀ᶠ l in φ, orbitMargin P n (x l) (o l):= eventually_dock _ (hx.tends (neg_neg_of_pos ha) hA) hk.inject n

lemma fit_old (k:L→Ortho): RateLE φ A (fun s=> spinning P X n (x s) (o s) (k s) v - spinning P X n (sole (o s)) (o s) (k s) (sole (shadowOld P m (x s) (o s) v): Labels S (fun _:Unit=>m))) ((weight d-m-1)*a):=by
   let f (i:Mode U.sector.derivatives)(l:L) : S.Field n :=∑ y∈(R.port.sheet i).support, ((R.port.sheet i) y * singleError U R m x o v l y (k l)) • U.sector.turns.act n (k l) (R.port.loaded i n)
   refine (RateLE.sum (f:=f) (S:=bands _ n) hA (fun i hi=>RateLE.sum hA (fun j _=>spin_old U R h hA v hx hk ha m n k j i))).congr ?_
   filter_upwards [margins U R hA hx hk ha n] with s hs; symm; rw [discrepancy_spin P R.law R.continuum U.phase.transport.motion _ _ hs]; exact Finset.sum_congr rfl (fun i hi=> Finset.sum_smul)
lemma fit_tint (k:L→Ortho): RateLE φ A (fun s=> spinning P X n (x s) (o s) (k s) (bar ρ v) - spinning P X n (sole (o s)) (o s) (k s) (sole (S.conj ρ m (shadowOld P m (x s) (o s) v)): Labels S (fun _:Unit=>m))) ((weight d-m-1)*a):=by
   let f (i:Mode U.sector.derivatives)(l:L) : S.Field n :=∑ y∈(R.port.sheet i).support, ((R.port.sheet i) y * errorColor U R m x o v l y (k l)) • U.sector.turns.act n (k l) (R.port.loaded i n)
   refine (RateLE.sum (f:=f) (S:=bands _ n) hA (fun i hi=>RateLE.sum hA (fun j _=>spin_tint U R h hA v hx hk ha m n k j i))).congr ?_
   filter_upwards [margins U R hA hx hk ha n] with s hs; symm; rw [discrepancy_spin P R.law R.continuum U.phase.transport.motion _ _ hs]; exact Finset.sum_congr rfl (fun i hi=> Finset.sum_smul)
end
end YM.OPE.Orbits
