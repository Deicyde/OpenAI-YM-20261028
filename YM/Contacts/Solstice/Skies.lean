import YM.Contacts.Solstice.Lanterns
/-!
# In the whole stage

Root formula forced to glue to subordinate test patches outside its small collar. Only invoke the
full Taylor-root prescription with projections at a *positive detector/spectator clearance*. Here
we instead show globally defined away or through that collar too: near each configuration take
its actual equality groups (when in root's collar one may also keep that root). This yields an
extension for all sufficiently small subtraction length about any position, **without extra
extension data outside the collars**. Doesn't assert availability of the root projection on these
arbitrary tests. Within their domains & on separate groups it agrees. This also provides global
consistency on ordinary full position families at varying centers.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory Manifold
variable {E W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {G: Gauge}{C : Family G}{F : Extraction.Order}{S: Table C.book}{Z : Final C F S}
variable {k : ℕ}{g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g}{o : Points k}{s B ε : ℝ}{d : Fin k→ℕ}
local notation "GN" => Normal.Group k

-- for arity zero use same output (empty partition of the empty group, ordinary unit expectation)
def localKernel (r : Route P Q I W)(M : Devices Z.sector.derivatives)(t : W→ Cells S d)(α : W→ Viewers Z) (p : SmoothTests E)(w : W)(x:E) := readExpr M.basis (spectator Z (α w)) (localImage M P Q (r.offset w) (r.length w) (t w) p x)
def kernel (P:E→ₗᵢ[ℝ] Points k)(g:GN)(M : Devices Z.sector.derivatives)(t : Cells S d) (α : Viewers Z)(o:Points k)(s:ℝ) (p:SmoothTests E)(x:E) := readExpr M.basis (spectator Z α) (localImage M P (root g) o s t p x)
-- used even on subgroups; when reading with exteriors, keep `θ`.
def Backdrop.vacuum ( _Z:Final C F S)(r:Route P Q I W): Backdrop S r (fun _:Empty=>0) where
   values _ _ _:=0
   labels j:=j.elim
   still _ _ _ _ _:=rfl
   held j:= j.elim
   bounds:=⟨0,fun j=>j.elim⟩
   continuous _ := continuousOn_const
   known j:= j.elim
lemma blank {δ : ℝ}{r:Route P Q I W} (h : Sober r δ) (hd:0<δ) : (Backdrop.vacuum Z r).Eligible δ:= ⟨hd, h, fun _ _ _ i=> i.elim, fun _ _ _ i=> i.elim⟩ -- apart fun implicit?
variable (M : Devices Z.sector.derivatives)
lemma local_image_eq (r : Route P Q I W) (T : W→ Cells S d)(α : W→ Viewers Z) (w p x): localKernel r M T α p w x= r.windings M ((Backdrop.vacuum Z r).polls M α) T (festive k) w p x:= by
   rw [← image_route,Backdrop.finalSight]; simp [Backdrop.haloWord,localKernel]

lemma under_root (T : System E (Expression Z.sector.derivatives) k)(x:E) (f : SmoothTests E)(hp : GroupsTest P Q o (tsupport f.val)) (h : plane g≤ LinearMap.range P.toLinearMap)(hh: Collapsed g o) : action x f (parcel (T.full P s) Q) = action x f (parcel (T.full P s) (root g)) := overlap_action _ _ s hp (top_groups _ _ h hh) x
lemma in_range (r : Route P Q I W) (α : W→ Viewers Z) (T : W→ Cells S d)(f : SmoothTests E)(w x) {δ:ℝ}(hd:0<δ) (hp:Sober r δ)(hv:tsupport f.val ⊆ r.stage w) (h : plane g≤ LinearMap.range P.toLinearMap)(he : Collapsed g (r.offset w)) : kernel P g M (T w) (α w) (r.offset w) (r.length w) f x= localKernel r M T α f w x:= by unfold kernel localKernel localImage; rw [under_root _ _ _ (onstage r w hv hd hp) h he]

private lemma still_given (T : Cells S d){W : Type} : Given (fun (_:W)=> T) := by
   obtain ⟨V,hV⟩:= Finite.bddAbove_range (fun i=> ‖T i‖); exact ⟨V,fun i _=> hV (Set.mem_range_self i)⟩

def totalTestOrder (d : Fin k→ℕ) (g : GN) := (2+(∑ j,d j))*g.card
lemma sufficient_total : stairs d Q ≤ totalTestOrder d g:= Nat.mul_le_mul_left _ (Nat.sub_le g.card _)
variable (H : Services C F S) (T : Cells S d) (α : Viewers Z)
variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]

variable (h:plane g ≤ LinearMap.range P.toLinearMap)(hp : Collapsed g o)
include h hp H
lemma clear_integral (H' : B ≤ M.clearance (∑ i,d i + 0))(L : Lights P g o s B) : ∃ C>(0:ℝ),∀ (f : SmoothTests E) (c:ℝ),tsupport f.val ⊆ L.region → Jet (totalTestOrder d g) univ f.val c → Dust (kernel P g M T α o s f) (C*c):= by
   let r:= L.clear.route; let v (w:Unit):= T; let a (w:Unit):=α; let ψ:= Backdrop.vacuum Z r; let hℱ:= any_power (T:=v) (ψ.hierarchy_cost (M:=M) (α:=a) (blank L.lit L.positive) H) (still_given T (W:=Unit)) (show r.Authority M d from H') H (ε:=1) one_pos
   obtain ⟨C,hC,hv⟩:= hℱ; let W:= r.bag d 1 () 1; have hx:0<W:= r.bag_pos () d one_pos; refine ⟨C*W,mul_pos hC hx,fun f c hL he=>?_⟩; have he:=hv (festive k) () f c hL (he.weaker sufficient_total) (fun i _=> rfl)
   refine (Dust.mono he (le_of_eq (by change C*c*W = _; ring))).transfer (Eventually.of_forall fun x=> ?_); exact Eq.trans (local_image_eq M r v a ..|>.symm) (in_range M r a v f () x L.positive L.lit hL h hp).symm
lemma glues_total {U : Set E} (hc : IsCompact U)(ha : B∈ Ioc (0:ℝ) 1)(hH : B ≤ M.clearance (∑ i,d i+0))(hs : 0<s∧2*s≤B): ∃ C>(0:ℝ),∀ (f:SmoothTests E)(c:ℝ), tsupport f.val ⊆ U → Jet (totalTestOrder d g) univ f.val c → Dust (kernel P g M T α o s f) (C*c):= by
   obtain ⟨V,hV⟩:= patch_need h hp ha hs hc
   let v(i:V):=interior i.val.region; obtain ⟨u,hu⟩:= SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,E) hc.isClosed v (fun i=> isOpen_interior) (by
      intro x hx; obtain ⟨i,hi,h⟩:= Set.mem_iUnion₂.mp (hV hx); exact Set.mem_iUnion.mpr ⟨⟨i,hi⟩,h⟩)
   let ψ(i:V) : SmoothTests E:= ⟨fun x=> (u i x:ℂ), Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp (u i).contMDiff)⟩
   let q:= totalTestOrder d g; choose A hA he using fun i:V=> controls (infSmooth (ψ i)) hc q
   choose C hC ht using fun i:V=> clear_integral M H T α h hp hH i.val
   let c(i:V):= C i * ((2:ℝ)^q*A i); let D:=max 1 (∑ i:V,c i)
   refine ⟨D, lt_of_lt_of_le zero_lt_one (le_max_left ..), fun f d' hx hh=>?_⟩; let z(i:V):= mask (ψ i) f
   let L:= kernel P g M T α o s; have hc(i:V) : tsupport (z i).val⊆ U:= (support_mask (ψ i) f).trans (Set.inter_subset_right.trans hx)
   have he'(i:V): Dust (L (z i)) (c i*d'):= by
       refine (ht i (z i) ((2:ℝ)^q*A i*d') ?_ ( ( (he i).times (hh.enlarge le_rfl (Set.subset_univ U) le_rfl) (infSmooth _) (infSmooth _)).recover (hc i))).mono (le_of_eq (by unfold c; ring))
       exact (support_mask (ψ i) f).trans (Set.inter_subset_left.trans ( ( ( ( closure_mono (fun x hx (h:(u i x)=0)=> hx ((congrArg Complex.ofReal h).trans Complex.ofReal_zero))) : tsupport (ψ i).val⊆ tsupport (u i))).trans ((hu i).trans interior_subset)))
       -- proof closing placeholder
   have hz:f=∑ i:V,z i:= by
       apply Subtype.ext; funext x; rw [sum_test]; change _=∑ i:V,(u i x:ℂ)*f.val x; rw [← Finset.sum_mul]; by_cases he:x∈U; rw [← Complex.ofReal_sum, u.sum_finsupport' _ he (Finset.subset_univ ..),Complex.ofReal_one,one_mul]; rw [notMem_support.mp (show x∉ support f.val from fun h=> he (hx (subset_closure h))), mul_zero]
   let k(i:V):=L (z i)
   have hm : L f= fun x=> ∑ i:V,k i x:= by
      funext x
      rw [hz]; unfold k; exact map_sum ( (readExpr M.basis (spectator Z α)).comp (Normal.under x (parcel ((waySystem P M o d T).full P s) (root g)))) z Finset.univ
   change Dust (L f) _; rw [hm]; apply Dust.mono (Dust.finite Finset.univ (fun i _=> he' i)); rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hh.pos
end YM.Contacts.Solstice
