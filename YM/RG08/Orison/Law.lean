import YM.RG08.Orison.Penny

/-! # Horizon restriction and adjacent-step coherence of limiting Fk unmarked. Scalar
 determinants not asserted by these normalized laws. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}(F:Horizon a){P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}{E:ℕ}
variable (L: Yamen.Supplies F P Z)(hM:Bill G P X a)(hh:Payment G P X Z a)(hA:Flat.Quorum (Flat.curve X) U 0 F A B d k c)
variable (P X) in
def report (Z:ChartRatio G)(E i:ℕ) := Orison.erase E (retreat F P X hg Z i)
variable (P X) in
def issue (Z:ChartRatio G)(E i:ℕ):= Orison.erase E (Orison.anchor F P X hg Z i)
variable (P X) in
def views (Z:ChartRatio G)(E i:ℕ):Scroll G:=- (Prism.bare (land (alumna F i)) +Steam.allG (land (poles F i)) (inlet (Yamen.branches (a:=a) i) (report F P X hg Z E (i+1)) Z) (land (skies F i)))

include L hM hh hA
local notation "Dp"=>report F P X hg Z E
local notation "Wp"=>issue F P X hg Z E
-- linear stamps enough to identify all nonconstant terms through e and coupling tickets.
private lemma valuation {e n i:ℕ}(he:e ≤ E)(hn:n ≤ e+2)(hi:E ≤ a.clock.J i)(hk:0<n)(x:Tape n (Market (Loc G 1))):
 Tendsto (fun j=>let M:=j+(i+1); plotter (Yamen.branches (a:=a) i) Z (F.H M (i+1)) (F.H M i) (fed F P X hg Z M (i+1)) e n x) atTop (𝓝 (views F P X hg Z E i e n x)):=by
 let N(j:ℕ):=j+(i+1); let g:= RG08.Supplies.stone a i
 let h:g.Branches a.clock.kernel G:=Yamen.branches _
 have hF: Shade E (fun j=>fed F P X hg Z (N j) (i+1)) (Dp (i+1)):=fidelity hg L hM hh hA (i+1) (i+1) le_rfl (hi.trans (a.fits.mono (by omega:i ≤ i+1)))
 obtain ⟨hV,hG,H⟩:= heated F L hA i (i+1) (by omega)
 obtain ⟨p,hp,hE⟩:= conditioned (h:=h) (Z:=Z) hG H hV hV hF he hk hn
 have hq:=Tone.field hE hk hp.le x
 obtain ⟨q,hQ,d,hd,⟨t,ht,h⟩,-⟩:= pedestal F L hA i (i+1) (by omega)
 have hs (y z:Market (Loc G 1)): Tendsto (fun j=> alumna F i (N j) y z) atTop (𝓝 (land (alumna F i) y z)):=by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hH:= hush.awe t d ht hd
    refine squeeze_zero (fun _=>norm_nonneg _) (fun j=>?_) hH.2
    have hr:= (h j).2.2;let a:=alumna F i (N j)- land (alumna F i)
    rw [Real.norm_eq_abs];change |a y z| ≤ _
    have he:bill (a y z) (q*delta 1 y.1 z.1)≤ ENNReal.ofReal (t j*d j):=(ENNReal.le_tsum (f:=fun x=> bill (a y (x,z.2)) (q*delta 1 y.1 x)) z.1).trans (hr.row y z.2)
    have hh:= (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hush.safe _ ht _) (tiny _ hd _))).mp he
    exact (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hQ.le (delta_nonneg ..)))).trans hh
 have hS : Tendsto (fun j=> bare (alumna F i (N j)) e n x) atTop (𝓝 (bare (land (alumna F i)) e n x)):=by
    unfold Prism.bare;split_ifs with hn he
    · subst n e; exact tendsto_const_nhds.mul (hs (x 0) (x 1))
    all_goals exact tendsto_const_nhds
 exact (hS.add hq).neg

theorem stock (i:ℕ)(hi:E ≤ a.clock.J i):Fair (Dp i) ∧ Fair (Wp i)∧ ∀ e ≤ E, ∀ r,
    (Dp i) r e=Nacre.send (Wp i) hg r e ∧
    (0 < r → r ≤ e+2 → demand (Wp i) e r= views F P X hg Z E i e r ∧ demand (Dp i) e r=Nacre.fraction (torque (Wp i) hg) (views F P X hg Z E i) e r):=by
 let N(j:ℕ):=j+(i+1)
 let Xd(j):Castle G:=wings F P X hg Z (N j) i
 let Ω:=Orison.honesty (F:=F) hg L hM hh hA i (i+1) (by omega) hi
 let Hx:=fidelity (F:=F) hg L hM hh hA i (i+1) (by omega) hi
 have H0 {e:ℕ}(he:e≤E)(r:ℕ)(x): Tendsto (fun j=>fed F P X hg Z (N j) i r e x) atTop (𝓝 (Dp i r e x)):=by obtain ⟨s,u,hE⟩:=Hx.cost e r he;exact Tone.field hE (Nat.zero_lt_succ _) u.le x
 have hm (e)(he:e≤E)(r:ℕ):Dp i r e=Nacre.send (Wp i) hg r e:=by
    ext x
    have hE:=H0 he r x
    have hv : (fun j=>send (Xd j) hg r e x) =fun j=>fed F P X hg Z (N j) i r e x:=by funext j;rw [mint_step (by unfold N;omega:i<N j)];rfl
    rw [←hv] at hE
    exact tendsto_nhds_unique hE (replenished hg Ω he x)
 have hb {e:ℕ}(he:e≤E)(r:ℕ)(hr:0<r)(hk:r ≤ e+2):demand (Wp i) e r=views F P X hg Z E i e r:=by
    funext t; obtain ⟨s,hs,H⟩:=Studio.castles Ω (k:=r) he hr
    have hc:= Tone.field H hr hs.le t
    let m(j):=F.H (N j)
    let h:(RG08.Supplies.stone a i).Branches a.clock.kernel G:=Yamen.branches _
    let c(j):=fed F P X hg Z (N j) (i+1)
    let f(j:ℕ):=plotter h Z (m j (i+1)) (m j i) (c j)
    have hT(j): demand (wings F P X hg Z (N j) i) e r=(f j) e r:=by
       obtain ⟨⟨hB⟩,hP⟩:=studio (X:=X) L.housed (N j) i hg (by unfold N;omega) (fun b=> L.herald _ _ _ (by unfold N;omega:i ≤ N j)) L.lodged (c j) (ship X hg L (by unfold N;omega:i+1 ≤ N j))
       exact (Sedan.harvest (lamp P X a i) (RG08.Supplies.stone a i) a.clock.kernel (m j (i+1)) (m j i) (c j) Z h hB _ hP hg).2.2 e r hr
    change Tendsto (fun j=>demand (wings F P X hg Z (N j) i) e r t) _ _ at hc; simp_rw [hT] at hc
    exact tendsto_nhds_unique hc (valuation F hg L hM hh hA he hk hi hr t)
 refine ⟨Hx.valid,Ω.valid,fun e he r=>⟨hm _ he r,fun hr hk=>⟨hb he _ hr hk,?_⟩⟩⟩
 rw [demand_mates (Dp i) (Nacre.send (Wp i) hg) (fun i x hx _=>hm i (hx.trans he) x),Nacre.send,sailed (torque (Wp i) hg) (torque_l _ hg Ω.valid) (Wp i) Ω.valid e r hr]
 unfold Nacre.fraction; refine Finset.sum_congr rfl fun k h' =>?_ ; have hq:k ≤ e:=Nacre.in_square ..|>.mp h';by_cases ht:r ≤ k+2
 · rw [hb (hq.trans he) _ hr ht]
 -- both zero. demand cap; allG eligible limit even for Γ kernel? mechanical needs city, easier via Steam.live arguments generic no city OR use hT & conditioned off field not granted. prove rank_off using no eligibility geom
 have hf {S:Patch}{h:S.Branches a.clock.kernel G}{f: Forms.Line (Market (Tack.Head S G))}{m:Kernel (Tack.Head S G) (Loc G 1)} (A:Castle G)(ha:Fair A): Steam.allG f (inlet h A Z) m k r = 0:=by
    unfold Steam.allG Steam.strict
    have hE(i):burn f (inlet h A Z) i k r=0:= Classical.byContradiction (fun h0=>ht ((Steam.live (inlet_eligible h Z ha.rails) i).head k r h0))
    have hv:=hE 0;rw [Steam.spark] at hv
    have hz:Forms.raft (repeatLine m r) 0=0:=by ext; simp [Forms.raft, Forms.vat]
    simp_rw [hv,Steam.cinder,hE,smul_zero,sum_const_zero,hz,add_zero]
 have hVs: views F P X hg Z E i k r=0:=by
    have hF:Fair (Dp (i+1)):= (Orison.fidelity (F:=F) hg L hM hh hA (i+1) (i+1) le_rfl (hi.trans (a.fits.mono (by omega: i ≤ i+1)))).valid
    unfold views
    change -(bare (land _) k r+_)=0
    rw [hf _ hF, Prism.bare,dif_neg (by omega),zero_add,neg_zero]
 have hg0:demand (Wp i) k r=0:= Classical.not_not.mp (fun h=>ht (RG08.Mount.demand_out Ω.valid.rails h).2.2)
 rw [hg0,hVs]
end YM.RG08.Orison
