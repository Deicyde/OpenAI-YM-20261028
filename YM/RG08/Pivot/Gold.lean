import YM.RG08.Fields.Surge
import YM.RG08.Door.Token
/-!
# Slotwise horizontal/null calculus at leading order

At finite n. Release to harmonics by wallet, no puncture masks or
representative metric comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Planned.PrimaryIntegral295
open scoped Topology BigOperators Classical
variable {c f : Side} {G : Gauge} {D n e r τ : ℕ} {R : ℝ} {i : Site c}
variable {U : EnvelopeU D R G r} {V : BoardU D R G}

-- carries prosodically only. Doesn't apply to same piece at higher order
abbrev recitalP (U : EnvelopeU D R G r) (i : Site c) (φ : Exam D) := stitch (plug φ R∘ U) c i
def Sober (U : EnvelopeU D R G r) := ∀ (m: Side) (o:Site m)(φ: Exam D) (a : Fin r) (w: Fin r→Link G m) (v : FreeResolvent.Vec G m 0),
    w a=gradient v → recitalP U o φ w=0
structure Gold (U : EnvelopeU D R G r) : Prop extends Toute U where
  lucid : Sober U

lemma sober_vetted (h: Marvel τ V) : Gold (V 0 r) := by
  refine ⟨seat_made h,fun m o φ i w v hL => ?_⟩
  let U:= V 0 r; let T:=plug φ R; let F:=recitalP U o φ
  have hv (n k):= Tidy.map T (h.hem n k)
  by_cases ht : r ≤ τ + 0
  swap
  · unfold recitalP; rw [not_ne_iff.mp (mt (h.cap 0 r) ht), show plug φ R ∘ (0:EnvelopeU D R G r)=(0:Shale _ _) from funext fun i=>map_zero _,st_zero]; rfl
  let p := τ - r
  let W : Screed ℝ (Loc G 1):=fun n k=> T ∘ V n k
  have hx: Loom.strand τ p W r=T ∘ U := by unfold Loom.strand; rw [if_pos (by unfold p; omega),show p+r-τ=0 by unfold p; omega]
  have hm (j:ℕ) (hv : j<r) : Loom.strand τ p W j=0 := if_neg (by unfold p; omega)
  let M:=fderiv ℝ (Stationary.dragged G m) 0
  let J:=bundleLink (m:=m) (G:=G)
  have he (x:Corn (Co m (Candles G))) : Tensor.diagonal F (M x)=Tensor.diagonal F (J x) := by
    have hh := Needle.lights (S:=W) hv (h.wardrobe m φ o) x p r
    unfold F M J U; unfold recitalP; change _=_
    refine Eq.trans ?_ (hh.trans ?_); · rw [hx]
    rw [hx, Finset.sum_eq_zero,sub_zero]
    intro i hi; rw [hm i (Finset.mem_range.mp hi), Needle.crock_hike _ x o]
    · simp [rootSong,Tensor.diagonal, Reflect.ink,PertExtension.Series.Radial.jet]
    exact Pens.zero ..
  have hy (Q : Corn (Co m (Candles G)) →L[ℝ] Link G m): Tensor.Sym (F.compContinuousLinearMap (fun _=>Q)) := fun i j => Tidy.sym (hv 0 r) o (Q∘i) j
  have hw:= Tensor.ext_diag _ _ (hy M) (hy J) (funext he)
  let u (a:Fin r):Corn (Co m (Candles G)):=fun j=> Sum.elim (fun c=> if a=i then -v (j.1,c) else 0) (fun c=> if a=i then 0 else w a (j.1,c)) j.2
  have hc (a : Fin r) : M (u a)=w a := by
    unfold M; rw [interpolate,first_gradient]; by_cases ha:a=i
    · subst a; rw [hL]
      rw [show restMap ℝ (u i)=0 from funext fun j=> if_pos rfl]
      rw [show siteMap ℝ (u i)= -v from funext fun j=> if_pos rfl]; unfold gradient; rw [mulVec_neg]; abel
    rw [show restMap ℝ (u a)=w a from funext fun j=> if_neg ha]
    rw [show siteMap ℝ (u a)=0 from funext fun j=> if_neg ha]; unfold gradient; rw [Matrix.mulVec_zero,sub_zero]
  have hk := DFunLike.congr_fun hw u
  change F (fun a=> M (u a))=F (fun a=> J (u a)) at hk
  rw [funext hc] at hk; exact hk.trans (F.map_coord_zero i (funext fun j=> if_pos rfl))

-- more general proof on V leading standalone internals
lemma grad_corner (p : Vec G c 0) (x : Site c) (i : Axis) (v : G.ColorIndex) :
    gradient p (x,coord i,v)=p (x+step i,vac,v)-p (x,vac,v) := by
  change component (tensor G (d 0 c)*ᵥ p) v (x,coord i)=_
  rw [component_mul,d_sites]; rfl
private def guess (c : Side) (F : Cover×Loc G 0→ℝ) : Vec G c 0:= fun i=>F (lift i.1,i.2)
def polarP (F : Cover×Loc G 0 → ℝ) (v : Cover×Loc G 1):= F (v.1+step (axisEquiv.symm v.2.1),vac,v.2.2)-F (v.1,vac,v.2.2)

private lemma harmony (F:Cover × Loc G 0 → ℝ) {s : ℕ} {A C b : ℝ} (hc : 0≤C) (hb:0≤b)
    (hv : ∀ x, ‖F x‖ ≤ C * dime s x.1) (H : ∀ i:Axis,∀ x:Cover,dime s (x+step i) ≤ A*dime s x) (m : Side)(x : Cover)(y : Axis)(j : G.ColorIndex):
    ‖gradient (guess m F) (wrap m x,coord y,j)‖ ≤ (b+C*A+C)*dime s x:= by
  rw [grad_corner]; let r:= wrap m x
  apply (norm_sub_le ..).trans
  have hp : lift (r+step y)=lift (wrap m (x+step y)) := by unfold r; rw [map_add,wrap_step]
  have hw : dime s (lift (r+step y)) ≤ A*dime s x := by rw [hp]; exact (coins_wrap _ s _).trans (H y x)
  have hz1:= hv (lift (r+step y),vac,j)
  have hz2:=hv (lift r,vac,j)
  have hl := add_le_add (hz1.trans (mul_le_mul_of_nonneg_left hw hc)) (hz2.trans (mul_le_mul_of_nonneg_left (coins_wrap x s m) hc))
  apply hl.trans
  have hu:=mul_nonneg hb (Carrier.liftCost_pos s x)
  unfold dime; linarith only [hu]
/-- Can test on polynomial fields (linearized Ward). -/
lemma Sober.cover_phi (hf : Sober U) (hp : Polished U) {φ : Exam D}
    {f : Fin r→ Cover×Loc G 1→ℝ} (k : Fin r) (F:Cover × Loc G 0 → ℝ) (h : f k=polarP F) {s : ℕ} {C : ℝ} (hc : 0≤C)
    (hv : ∀ x, ‖F x‖ ≤ C * dime s x.1) {b : Fin r→ℝ} (hB : 0≤b) (hh : ∀ i x, ‖f i x‖≤b i*dime s x.1) :
    wallet (plug φ R∘ U) f=0 := by
  let n:=even_side
  let z (m : Side) i:Link G m := if i=k then gradient (guess m F) else fun x=> f i (lift x.1,x.2)
  have he (i : Fin r)(p:Fare G): Tendsto (fun a=> z (n a) i (wrap (n a) p.1,p.2)) atTop (𝓝 (f i p)) := by
    refine EventuallyEq.tendsto ?_
    rcases p with ⟨x,y,v⟩; obtain ⟨c,rfl⟩:=axisEquiv.surjective y
    filter_upwards [eventually_unfold n evenings_grow x,eventually_unfold n evenings_grow (x+step c)] with a ha hb
    let m:=n a
    have hu : lift (wrap m x + step c)= x+step c:= by rw [← show wrap m (x+step c)=wrap m x + step c from (map_add (wrap m) x (step c)).trans (by rw [wrap_step m c])]; exact hb
    unfold z; split
    next ht=> subst i; rw [coord_map,grad_corner,h]; change guess _ _ (wrap m x+step c,_) - guess _ _ (wrap m x,_)=_; unfold guess polarP
              dsimp only; rw [hu,show lift (wrap m x)=_ from ha,show axisEquiv.symm (coord c)=c from axisEquiv.symm_apply_apply _]
    next ht=> change f i (lift (wrap _ x),_)= _; rw [ha]
  obtain ⟨A,hA,H⟩ := coin_step s
  let d (i:Fin r):=b i+C*A+C
  have hD i : 0≤ d i:= by have hh :0≤ b i:= hB i; unfold d; positivity
  have hx (i x p a): ‖z (n a) i (wrap (n a) x,p)‖ ≤ d i*dime s x := by
    rcases p with ⟨b',c'⟩; obtain ⟨y,rfl⟩:= axisEquiv.surjective b'; let m:=n a
    unfold z; split
    next hi=>
      exact harmony F hc (hB i) hv H (n a) x y c'
    next hi=>
      refine (hh i (lift (wrap (n a) x),axisEquiv y,c')).trans (mul_le_mul ?_ (coins_wrap x s (n a)) (Carrier.liftCost_pos ..) (hD i))
      unfold d; nlinarith
  have ht:= wallet_limit evenings_grow (polished_fun hp (plug φ R)) he s (show 0≤d from hD) hx
  refine tendsto_nhds_unique_of_eventuallyEq ht tendsto_const_nhds (Eventually.of_forall fun i=>?_)
  exact hf (n i) 0 φ k (z (n i)) _ (if_pos rfl)

end YM.RG08.Pivot
