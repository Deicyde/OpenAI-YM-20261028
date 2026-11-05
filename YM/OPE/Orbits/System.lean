import YM.OPE.Orbits.Gain

/-! Intrinsic homogeneous channels and exact finite truncation compatibility
of the orbit Reader (`fresh`), interpreted by the ground algebra and by each
physical phase/unselected kernel. No change of basis depending on the tested
spectators. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Table Extraction
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
namespace Reader
variable {G:Gauge}{L:Register G}{S:Table L}{Q:DiffPlan S}{ρ:S.RealSpin}{X:S.Rotation}{I:Type}[Fintype I]{d:I→ℕ}
    (R:Reader Q X ρ)

def actor (m:ℕ)(i:R.channels m) : S.Field m := R.basis m i

def coef (m:ℕ)(i:R.channels m)(x:I→E4)(v:Labels S d)(o:E4):ℂ :=
     (R.basis m).repr (⟨R.fresh m x o v,R.fresh_mem m x o v⟩:R.stratum m) i
lemma assemble (m:ℕ)(x:I→E4)(v:Labels S d)(o:E4): ∑ i:R.channels m, (R.coef m i x v o) • R.actor m i = R.fresh m x o v:= by 
    have ht:=congr_arg ((R.stratum m).subtype) ((R.basis m).sum_repr ⟨R.fresh m x o v,R.fresh_mem _ _ _ _⟩); simp only [map_sum,map_smul] at ht; exact ht -- map_sum not defeq

def packet (m:ℕ)(x:I→E4)(v:Labels S d)(o:E4): S.Field m :=
    ∑ j:Fin (m+1),Q.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt) (R.fresh j.val x o v)
lemma filtered_packet (j m:ℕ)(h:j≤ m)(x:I→E4)(v:Labels S d)(o:E4):R.cutTest j m (R.packet m x v o)=R.fresh j x o v:=by
    rw [packet,map_sum]; let u(c:Fin (m+1)):=R.fresh c.val x o v
    let i:Fin (m+1):= ⟨j,Nat.lt_succ_of_le h⟩
    change ∑ q:Fin _,R.cutTest j m (Q.rise (d:=q.val) _ (u q))= R.fresh j x o v
    rw [Finset.sum_eq_single i] -- inspect Finset.sum_eq_single side order
    · rw [R.cut_rise] -- with i substituted
      exact R.test_fixes _ _ (R.fresh_mem _ _ _ _)
    · intro b hb hbi; rw [R.cut_rise]; exact R.test_orthogonal _ _ (u b) (R.fresh_mem _ _ _ _) (fun he=> hbi (Fin.ext (by exact he.symm)))
    exact fun hb=>False.elim (hb (Finset.mem_univ i))
lemma packet_single (m j:ℕ)(h:j≤ m)(v:S.Field j): R.packet m (sole 0) (sole v : Labels S fun _:Unit=>j) 0=Q.rise h v :=by
    unfold packet; simp_rw [R.single]; exact R.reconstruct m j h v
/-- Smoothness of every finite collection on its eventual joint separated
compact. This is pointwise smoothness including at ties in individual axes;
we do not put ties inside a point limit at finite cutoff. -/
lemma coef_smooth (m:ℕ)(i:R.channels m){x:I→E4}{o:E4}(h:orbitMargin R.port m x o)(v:Labels S d):ContDiffAt ℝ ∞ (fun q:(I→E4)× E4=>R.coef m i q.1 v q.2) (x,o):=by
    let M:= (R.basis m).coord i; let g:= R.knife m |>.codRestrict (R.stratum m) (fun x=>R.knife_mem m x)
    let f:S.Field m→L[ℝ]ℂ := (LinearMap.toContinuousLinearMap (M ∘ₗ g)).restrictScalars ℝ
    let V(q:(I→E4)×E4):=checkReal R.port R.law R.continuum m q.1 q.2 v
    apply (ContDiffAt.comp (𝕜:=ℝ) (g:=f) _ f.contDiff.contDiffAt (smoothReal m R.law R.continuum x o v h))
end Reader
open Reader

variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    {I J:Type}[Fintype I][Fintype J] {d:I→ℕ}{e:J→ℕ} (x:I→E4)(o:E4)(v:Labels S d)(y:J→E4)(w:Labels S e)

/-- Whole tested truncation in physical homogeneous basis. Sum order fixed. -/
def trunc (T:Table C.book)(U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (m:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(y:J→E4)(w:Labels S e):ℂ:=
    ∑ j:Fin (m+1),∑ i:R.channels j.val,(R.coef j.val i x v o)* whole T (sole o) ((sole (R.actor j.val i)):Labels S (fun _:Unit=>j.val)) y w
private lemma trunc_fields (T:Table C.book)(m:ℕ): trunc T U R m x o v y w=∑ j:Fin (m+1), upon T _ o y w (R.fresh j.val x o v):=by
    refine Finset.sum_congr rfl fun j hj=> ?_; rw [← R.assemble j.val x v o,map_sum]; exact Finset.sum_congr rfl (fun i hi=>by rw [map_smul]; rfl)
lemma packet_read (r:Viewers U)(m:ℕ)(hm:Injective (beside (sole o) y)): upon (spectator U r) m o y w (R.packet m x v o)=trunc (spectator U r) U R m x o v y w:=by
    unfold packet; rw [trunc_fields,map_sum]; exact Finset.sum_congr rfl fun j _=> upon_rise U R _ _ _ _ _ _ hm
lemma tested_fields (r:Viewers U)(m:ℕ): balance U (spectator U r) R m x o v y w = whole (spectator U r) x v y w - trunc (spectator U r) U R m x o v y w := by rw [balance,trunc_fields]

def algebraError (m:ℕ): U.α.unselected.algebra :=
    viewing U (beside x y) (beside (names v) (names w)) -
       ∑ j:Fin (m+1), viewing U (beside (sole o) y) (beside (names ((sole (R.fresh j.val x o v)):Labels S (fun _:Unit=>j.val))) (names w))
lemma read_algebra (r:Viewers U) {x:I→E4}{v:Labels S d}{y:J→E4}{w:Labels S e} (hx:Injective (beside x y)):glance U r (viewing U (beside x y) (beside (names v) (names w))) = whole (spectator U r) x v y w:= by rw [whole_observed]; exact glance_sees U r _ _ hx
lemma see_algebra (r:Viewers U)(m:ℕ)(hx:Injective (beside x y))(hy:Injective (beside (sole o) y)):
    glance U r (algebraError U R x o v y w m) = balance U (spectator U r) R m x o v y w := by rw [algebraError,map_sub,map_sum,read_algebra U r hx,balance]; apply congr_arg (_-·); exact Finset.sum_congr rfl (fun j hj=>read_algebra U r (v:=(sole (R.fresh j.val x o v):Labels S (fun _:Unit=>j.val))) hy)

/-- Convention for all phase kernels at once once a `Final` and Reader have
been produced. `r` here is the viewer path index in `formula`, not a prescribed
length. We suppress the declared length argument of the coefficients since
these exact homogeneous readouts don't need it (even after moving exterior
positions). -/
def formula (m:ℕ)(r:Viewers U) := whole (spectator U r) x v y w - trunc (spectator U r) U R m x o v y w
lemma formula_seen (m:ℕ)(r:Viewers U)(hx:Injective (beside x y)) (he:Injective (beside (sole o) y)):
    glance U r (algebraError U R x o v y w m)=formula U R x o v y w m r:=by rw [formula,see_algebra _ _ _ _ _ _ _ _ _ hx he,← tested_fields]
end YM.OPE.Orbits
