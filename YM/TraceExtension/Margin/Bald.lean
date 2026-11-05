import YM.TraceExtension.Margin.Pillar
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
structure Jade (R:Rep G n)(t:ℝ)(V:CrG G n)(a:Axis):Prop where
   holds: Bounce V
   pace: Cubc R t (V 0)
   heart: Cubc R t (twig a V 0)
structure Scraps(R:Rep G n) (t:ℝ)(J:Dart G n):Prop where
    club : Club R t (Meld J t)
    flames (a:Axis): Jade R t (pluck (rim t) J a) a
    floors (a b i:Axis) : Jade R t (pluckD (rim t) J a b i) i
lemma Ponting(h:Scraps R t J)(hv:5 ≤ R.p.order)(hx:Nonwrapping (tempQ t (n:=n)) 0)(hs:40 ≤ n.val)(hG:G.Simple): ∃ w,Walt F Z H t (Meld J t) w ∧ rho hG (bareVector w)=0:=by
   let U:= cardX F H t (Meld J t); have hp : 4 ≤ R.p.order:=by omega
   have he(x y:Axis) : R4 R t (Meld J t x y 0):= Real_regular (h.club.peek x y).puff.regular
   have ht(a b:Axis)(hx':a<b): U a b= U b a:= by
        let v(k:Axis):=pluckD (rim t) J a b k; let y k:= twig k (v k) 0; let Y:=∑ k:Axis,y k
        have hc : ∑ k:Axis,DCard H F t (y k)=0:= Finset.sum_eq_zero (fun i _=> TW F i (v i) (h.floors a b i|>.pace) ((h.floors a b i).heart) ((h.floors a b i).holds) hx hG hs hp)
        have hD: Meld J t a b 0=Y+Meld J t b a 0:=by apply eq_add_of_sub_eq; unfold Y y; rw[←Finset.sum_apply (g:= fun k=> twig k (v k))]; exact congr_fun (spirit (rim t) J a b hx') 0
        obtain ⟨h₁,h₂⟩:= cheer F (H:=H) univ y hp (fun i _=>Real_regular (h.floors _ _ _|>.heart.puff.regular))
        unfold U cardX DCard; rw[hD, (plush (tempQ t) _ _ R 0).1, Push.Local.project_add H 0 h₁ (he b a) hp,map_add]; change DCard H F t Y+_= _; rw[ ← show 0=DCard H F t Y from (h₂.trans hc).symm,zero_add]
   have ht(i j):U i j=U j i:=by rcases lt_trichotomy i j with h|h|h; exact ht _ _ h; rw[h]; exact (ht _ _ h).symm
   obtain ⟨w,hV⟩:=pruned (F:=F) (Z:=Z) h.club hv hx hs hG ht
   let J':= Meld J t; have hA:= cones (rim t) J; refine ⟨w,hV,honestW F hV (zero_club F (v:=fun i=>J' i i 0) (w:=pluck (rim t) J) hp (fun i=>(h.flames i).pace) (fun i=> (h.flames i).heart) (fun i=>he i i) (fun i=>(h.flames i).holds) ?_ hG hs hx) hG⟩
   rw [←Finset.sum_apply (g:=fun i=> J' i i),← Finset.sum_apply (g:=fun i=>twig i (pluck (rim t) J i))]; exact congr_fun hA 0
lemma drumK(x:ℝ): drumA x=x*drumA 1:=by unfold drumA; rw[Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
open Planned.AtomRegular.Foliage WardBin WardBin.Wheels WardBin.Lies Next.Fluctuations Work.E01
lemma shred (G:Gauge)(S:Stage)(T:Collar G S.order) : ∀ᶠ x:ℝ in atTop, ∀ (n:Side)(v:ℝ)(R:Rep G n)(J:Dart G n), Age S x v R→ Sight x R J→ 20*(high x+10)< n.val → Scraps R x J:=by
   obtain ⟨D,hD,H⟩:= shimmer G S S.order le_rfl T
   obtain ⟨Z,hZ,h⟩:= cast_shape G S 48 0 T
   let f:= thinM; have hv :ConstMass (1/200) f:= waveM _
   have ht:ConstMass (1/200) (fun x=> drumA (f x)):=by simp_rw [funext (fun x=> (drumK (f x)).trans (mul_comm ..))]; exact hv.times _ (sum_nonneg (fun _ _=> by positivity))
   filter_upwards [sense G D S.order hD,hv (1/50) (by norm_num), ht (1/50) (by norm_num), (hv.gather hv) (1/50) (by norm_num),h,eastP,wnt S (Cube.fee T) (Cube.fee_one T) S.order,radiusB_tendsto.eventually_ge_atTop 2] with x he hv hP hp' hX ht hW hh n v R J hr hs hM
   obtain ⟨hz,hp,hA,hy⟩:=he n J R hs
   obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩:=hX 1100 le_rfl (by unfold towerH; omega) v n R hr
   let a:= eastD x; have ha:0 ≤ eastD x:= div_nonneg ht.1.le (by norm_num); have ha':eastD x ≤ 1:=(div_le_self ht.1.le (by norm_num)).trans ht.2
   have hV(X:Peat G n)(k:ℕ)(C:ℝ)(hk:k ≤ high x)(hv:C≤ Zn.wideM x)(h:Splendor X (sprout 0 k) S.order C D):Cubc R x X:= (H x v n R hr h₅ (by omega) _ X (Or.inl (h.up (sprout_mono _ hk) le_rfl))).plus (hW.1 _ hv) hv
   have hK:puff x+1+4≤ high x:=by unfold high Zn.puff; omega
   have H₁(F H: CrG G n)(t:ℝ)(a:Axis)(h:Turret.Bond F H S.order (Zn.puff x) (eastD x) (thinM x) t D): Jade R x H a:=⟨h.running,hV _ _ _ (by omega) hv.2 (h.read _), hV _ _ _ (by omega) hp'.2 ((h.suffix a ha ha').read 0)⟩
   exact ⟨⟨fun i j=> hV _ _ _ (by omega) hv.2 ((hz i j).read 0), fun i j=> (hz i j).running,fun i j=> hV _ _ _ hK hP.2 ((draftA (hz i j) i ha ha').read 0),fun i=> hV _ _ _ hK hv.2 ((hy i).read 0)⟩,fun i=> H₁ _ _ _ _ (hp i),fun i j k=> H₁ _ _ _ _ (hA i j k)⟩
end YM.Trace.Margin
