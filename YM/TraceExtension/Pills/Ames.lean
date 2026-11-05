import YM.TraceExtension.Pills.Hazy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{I:Type}
lemma spunok (s:Seat n)(p:Wo G)(o:Site n): Drift _ (fun U:Config G n=> p.unmasked (s.view U) o):=by
    intro X _ _ U x hp; obtain ⟨f,hf,H⟩:= roundBill G G.colorScale G.colorScale_pos.le 0 2
    apply (H X n o p (s.view ∘ U) x ?_).analytic
    apply rollA (U:=U) s; intro i; refine ⟨hp i,fun t ht=>?_⟩; obtain rfl:t=0:=by omega
    rw[norm_iteratedFDeriv_zero]; exact (SectorAffine.mat_paid ..).le
def miniC (p:Wo G) (s:Seat n): Peat G n:= fun U=>VerifiedReset.factor * p.unmasked (s.view U) 0
lemma paper_at(L:Finset I)(p:I→Wo G): paper (n:=n) L p=∑ v∈L, ∑ s:Seat n, miniC (p v) s:=by
    ext1 U; rw [paper, Finset.mul_sum]; simp only[Finset.sum_apply]; apply sum_congr rfl fun j _=>?_; unfold miniC; rw[←Finset.mul_sum]; apply congr_arg (VerifiedReset.factor * ·); rw [Fintype.sum_prod_type,blatch]
    refine sum_congr rfl fun s _=>?_ ; symm; rw[← Equiv.sum_comp s.actEquiv.toEquiv]; apply sum_congr rfl fun x _=>?_ ; change (p j).unmasked (Seat.view (s,s.act x) U) 0=_; rw [roll_c, rollate]
lemma stood_w (L:Finset I)(p:I→Wo G): Drift _ (paper L p (n:=n)):=by
    rw [paper_at]; intro X _ _ U x H; simp only[Function.comp_def,Finset.sum_apply,miniC]; exact ContDiffAt.sum (fun i _=> ContDiffAt.sum fun j _=> contDiffAt_const.mul (spunok j (p i) _ X _ _ H))
lemma bankers (U V:Peat G n) (h:Drift _ U)(he: Drift _ V){S:Gal G n}: rill (U+V) S=rill U S + rill V S:=by
    ext1 A; unfold rill beamG
    have hv':Army (fun x:Link G n=>input G n x*A) 0:= (Army.powL (v:=id) contDiffAt_id).mul (Army.park A _)
    rw [show bal A (U+V)=bal A U+ bal A V from rfl, fderiv_add]; rfl; exact (h _ _ _ hv'|>.differentiableAt (by simp)); exact (he _ _ _ hv'|>.differentiableAt (by simp))
lemma roundCov(L:Finset I)(p:I→Wo G)(h:∀ i∈L,(p i).Invariant): GaugeInvariant (paper L p (n:=n)):=by
    intro W U; rw[paper_at]; simp only [Finset.sum_apply]; refine sum_congr rfl fun i hi=> sum_congr rfl fun j _=> ?_; simp only [miniC,Seat.view,Push.Local.pull_gauge,Atom.unmasked,Work.F05.slot_gauge]; exact congr_arg (_*·) (h i hi _ _)
lemma blank_h (L:Finset I)(p:I→Wo G)(hp: ∀ i∈ L,(p i).Invariant)(h:hush L p){Q:Sway G n}{V:Support n}{Y:Axis→Gal G n}(hy:∀ a, Clouded (Y a) V)(hG:G.Simple){M t:ℕ}(hs:Nonwrapping V 0)(hh: V⊆ sprout 0 t)(hv:2*(t+1+1+M)+6< n.val)(ht:∀ i∈L,(p i).length ≤ M) (a:G.ColorIndex) (hw:∀ i, LocalOn V (rill (paper L p) (Y i))): Loft.Holt a (fun i=> rill (paper L p) (Y i) ∘ input G n) =0:=by
    let T :=paper L p (n:=n); let Vw(i):= rill T (Y i)
    have hz(i):Vw i ∈ loom G n:= rill_lo (stood_w L p) (roundCov L p hp) (hy i) hG
    have hcT: Cleric T:=⟨stood_w L p _ (input G n) _ (Army.powL (v:=id) contDiffAt_id),fun _ _ _ _ _ _ _ _ _ _ _ _=>Eventually.of_forall fun _=> roundCov L p hp _ _⟩
    have h0: bal (1:Config G n) T=T ∘ input G n:= funext fun x=>by simp[bal]
    have ht'(X Y:Link G n): X ⬝ᵥ (Kbody T*ᵥ Y)=sheen T X Y:=by unfold sheen Kbody beamH; rw[h0]; have hp:=detracts (pocket _) (T∘input G n) 0 X Y; rwa [cash_pocket,cash_pocket] at hp
    have hr(i:Axis): Cleric (Vw i):= (hz i).1
    have hx(u v:Track)(k y:ℕ)(hk:k ≤2)(hp':y ≤2)(i j:Axis): sheen (Vw i) (XR u j a k) (XR v j a y)=0:=by
       let X':=XR (n:=n) u j a k; let Y':=XR (n:=n) v j a y; unfold sheen; unfold Vw
       rw [show iteratedFDeriv _ _ _ _ _ = _ from (rill_state hG hcT (Y:=Y i) (hy i|>.rises.1)).2 X' Y',ht', ht']
       rw [show sheen T _ Y'=0 from combM L p h _ _ (stifleW (hy i) hh X') (fun s=> fibres s v j a hv y hp') ht, show sheen T _ X'=0 from combM L p h _ _ (stifleW (hy i) hh Y') (fun s=> fibres s u j a hv k hk) ht,add_zero]
    have hg(i j:Axis)(x: Loft.Land): neap 3 (mush j a (Vw i)) 0 x=0:=by
       rw[chant3]; simp_rw [moon_w]; rw [show sheen (Vw i) _ (XR _ _ _ 0) = 0 from stitch0 _ _ _ (hr i) (hw i) hs hG (by omega) _, sheen_symm (Vw i) (hr i) (XR _ _ _ 0), show sheen (Vw i) _ (XR _ _ _ 0)=0 from stitch0 _ _ _ (hr i) (hw i) hs hG (by omega) _,hx _ _ _ _ (by omega) (by omega),hx _ _ _ _ (by omega) (by omega)]; simp
    rw[Kits.height a hs hG (by omega) _ hr hw]; unfold suite; change (∑ d:Axis,∑ i:Axis,if d=i then _ else ∑ j:Axis, Deb (fun t=> neap 3 (mush i a (Vw j)) 0 _))=0
    simp_rw[hg]; change (∑ d:Axis,∑ i:Axis,if d=i then (0:ℂ) else ∑ j:Axis, Deb 0 )=0; simp
end YM.Trace.Pills
#print axioms YM.Trace.Pills.blank_h
